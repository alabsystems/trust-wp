// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive PureExpr walker for trigger candidate collection.
//!
//! Walks the expression tree tracking which bound variables each sub-expression
//! covers, respecting variable shadowing from quantifiers, let bindings,
//! match patterns, and closure parameters.

use std::collections::HashSet;

use trust_wp_core::formula::{Pattern, PureExpr};

use super::coverage::{
    CandidateSink, DepthOverflowPolicy, NoCandidateSink, QuantifiedVarCoverage, QuantifiedVarIndex,
    TriggerCandidate, VecCandidateSink,
};
use crate::encoder::MAX_ENCODING_DEPTH;

/// Insert pattern bindings into `shadowed`, returning only the names that
/// were actually new (for rollback via `remove`).
fn shadow_pattern_bindings(pattern: &Pattern, shadowed: &mut HashSet<String>) -> Vec<String> {
    let names = pattern.bound_names();
    let mut added = Vec::new();
    for name in names {
        if shadowed.insert(name.to_string()) {
            added.push(name.to_string());
        }
    }
    added
}

pub(super) fn collect_quantified_coverage(
    expr: &PureExpr,
    index: &QuantifiedVarIndex<'_>,
    shadowed: &mut HashSet<String>,
    depth: usize,
) -> QuantifiedVarCoverage {
    let mut sink = NoCandidateSink;
    collect_quantified_coverage_with_sink(
        expr,
        index,
        shadowed,
        depth,
        DepthOverflowPolicy::FullCoverage,
        &mut sink,
    )
}

fn collect_method_call_coverage<'a, S: CandidateSink<'a>>(
    receiver: &'a PureExpr,
    args: &'a [PureExpr],
    index: &QuantifiedVarIndex<'_>,
    shadowed: &mut HashSet<String>,
    depth: usize,
    overflow_policy: DepthOverflowPolicy,
    sink: &mut S,
) -> QuantifiedVarCoverage {
    let mut coverage = collect_quantified_coverage_with_sink(
        receiver,
        index,
        shadowed,
        depth,
        overflow_policy,
        sink,
    );
    for arg in args {
        let arg_coverage = collect_quantified_coverage_with_sink(
            arg,
            index,
            shadowed,
            depth,
            overflow_policy,
            sink,
        );
        QuantifiedVarIndex::merge_coverage(&mut coverage, arg_coverage);
    }
    coverage
}

fn collect_logic_fn_call_coverage<'a, S: CandidateSink<'a>>(
    args: &'a [PureExpr],
    index: &QuantifiedVarIndex<'_>,
    shadowed: &mut HashSet<String>,
    depth: usize,
    overflow_policy: DepthOverflowPolicy,
    sink: &mut S,
) -> QuantifiedVarCoverage {
    let mut coverage = index.empty_coverage();
    for arg in args {
        let arg_coverage = collect_quantified_coverage_with_sink(
            arg,
            index,
            shadowed,
            depth,
            overflow_policy,
            sink,
        );
        QuantifiedVarIndex::merge_coverage(&mut coverage, arg_coverage);
    }
    coverage
}

#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::too_many_lines
)]
fn collect_quantified_coverage_with_sink<'a, S: CandidateSink<'a>>(
    expr: &'a PureExpr,
    index: &QuantifiedVarIndex<'_>,
    shadowed: &mut HashSet<String>,
    depth: usize,
    overflow_policy: DepthOverflowPolicy,
    sink: &mut S,
) -> QuantifiedVarCoverage {
    if depth > MAX_ENCODING_DEPTH {
        return match overflow_policy {
            DepthOverflowPolicy::EmptyCoverage => index.empty_coverage(),
            DepthOverflowPolicy::FullCoverage => index.full_coverage(),
        };
    }
    let next = depth.saturating_add(1);
    let depth_score = depth as i32;
    match expr {
        PureExpr::Var(name, _) => {
            if shadowed.contains(name.as_str()) {
                index.empty_coverage()
            } else {
                index.coverage_for_var(name)
            }
        }
        PureExpr::MethodCall {
            receiver,
            method: _,
            args,
        } => {
            let coverage = collect_method_call_coverage(
                receiver,
                args,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            if !coverage.is_empty() {
                let score =
                    -(QuantifiedVarIndex::coverage_count(&coverage) as i32 * 10) + depth_score * 3;
                sink.push(expr, coverage.clone(), score);
            }
            coverage
        }
        PureExpr::LogicFnCall { name: _, args } => {
            let coverage =
                collect_logic_fn_call_coverage(args, index, shadowed, next, overflow_policy, sink);
            if !coverage.is_empty() {
                let score = -(QuantifiedVarIndex::coverage_count(&coverage) as i32 * 10)
                    + depth_score * 3
                    - 5;
                sink.push(expr, coverage.clone(), score);
            }
            coverage
        }
        PureExpr::BinOp(l, _, r) => {
            let mut coverage = collect_quantified_coverage_with_sink(
                l,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            let right = collect_quantified_coverage_with_sink(
                r,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            QuantifiedVarIndex::merge_coverage(&mut coverage, right);
            coverage
        }
        PureExpr::UnOp(_, inner) => collect_quantified_coverage_with_sink(
            inner,
            index,
            shadowed,
            next,
            overflow_policy,
            sink,
        ),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            match inner.as_ref() {
                // Preserve wrappers around call-shaped triggers so the emitted
                // pattern matches the body encoding exactly. (#1142, #1649)
                PureExpr::MethodCall { receiver, args, .. } => {
                    let coverage = collect_method_call_coverage(
                        receiver,
                        args,
                        index,
                        shadowed,
                        next,
                        overflow_policy,
                        sink,
                    );
                    if !coverage.is_empty() {
                        let score = -(QuantifiedVarIndex::coverage_count(&coverage) as i32 * 10)
                            + depth_score * 3;
                        sink.push(expr, coverage.clone(), score);
                    }
                    coverage
                }
                PureExpr::LogicFnCall { args, .. } => {
                    let coverage = collect_logic_fn_call_coverage(
                        args,
                        index,
                        shadowed,
                        next,
                        overflow_policy,
                        sink,
                    );
                    if !coverage.is_empty() {
                        let score = -(QuantifiedVarIndex::coverage_count(&coverage) as i32 * 10)
                            + depth_score * 3
                            - 5;
                        sink.push(expr, coverage.clone(), score);
                    }
                    coverage
                }
                _ => collect_quantified_coverage_with_sink(
                    inner,
                    index,
                    shadowed,
                    next,
                    overflow_policy,
                    sink,
                ),
            }
        }
        PureExpr::Ite(c, t, e) => {
            let mut coverage = collect_quantified_coverage_with_sink(
                c,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            let then_coverage = collect_quantified_coverage_with_sink(
                t,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            QuantifiedVarIndex::merge_coverage(&mut coverage, then_coverage);
            let else_coverage = collect_quantified_coverage_with_sink(
                e,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            QuantifiedVarIndex::merge_coverage(&mut coverage, else_coverage);
            coverage
        }
        PureExpr::Forall { var, body, .. } | PureExpr::Exists { var, body, .. } => {
            let was_new = shadowed.insert(var.clone());
            let coverage = collect_quantified_coverage_with_sink(
                body,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            if was_new {
                shadowed.remove(var);
            }
            coverage
        }
        PureExpr::Match { scrutinee, arms } => {
            let mut coverage = collect_quantified_coverage_with_sink(
                scrutinee,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            for arm in arms {
                let added = shadow_pattern_bindings(&arm.pattern, shadowed);
                let arm_coverage = collect_quantified_coverage_with_sink(
                    &arm.body,
                    index,
                    shadowed,
                    next,
                    overflow_policy,
                    sink,
                );
                QuantifiedVarIndex::merge_coverage(&mut coverage, arm_coverage);
                for name in &added {
                    shadowed.remove(name);
                }
            }
            coverage
        }
        PureExpr::Let { var, value, body } => {
            let mut coverage = collect_quantified_coverage_with_sink(
                value,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            let was_new = shadowed.insert(var.clone());
            let body_coverage = collect_quantified_coverage_with_sink(
                body,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            if was_new {
                shadowed.remove(var);
            }
            QuantifiedVarIndex::merge_coverage(&mut coverage, body_coverage);
            coverage
        }
        PureExpr::LetAssume {
            assumption, body, ..
        }
        | PureExpr::LetObligation {
            obligation: assumption,
            body,
            ..
        } => {
            let mut coverage = collect_quantified_coverage_with_sink(
                assumption,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            let body_coverage = collect_quantified_coverage_with_sink(
                body,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            QuantifiedVarIndex::merge_coverage(&mut coverage, body_coverage);
            coverage
        }
        PureExpr::Closure { params, body } => {
            let mut added = Vec::new();
            for (param, _) in params {
                if shadowed.insert(param.clone()) {
                    added.push(param.clone());
                }
            }
            let coverage = collect_quantified_coverage_with_sink(
                body,
                index,
                shadowed,
                next,
                overflow_policy,
                sink,
            );
            for name in &added {
                shadowed.remove(name);
            }
            coverage
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => index.empty_coverage(),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => index.empty_coverage(),
    }
}

pub(super) fn collect_trigger_candidates_with_index<'a>(
    expr: &'a PureExpr,
    index: &QuantifiedVarIndex<'_>,
    shadowed: &mut HashSet<String>,
    depth: usize,
    candidates: &mut Vec<TriggerCandidate<'a>>,
) {
    let mut sink = VecCandidateSink { candidates };
    let _ = collect_quantified_coverage_with_sink(
        expr,
        index,
        shadowed,
        depth,
        DepthOverflowPolicy::EmptyCoverage,
        &mut sink,
    );
}
