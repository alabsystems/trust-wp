// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parsed call-edge collection from logic function expressions.
//!
//! Walks `PureExpr` trees to extract structured call edges with actual arguments
//! and path conditions, used by variant-decrease proofs for mutual recursion.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{BinOp, CaptureAvoidingSubstOptions, Pattern, PureExpr, UnOp};

use super::{
    graph::{receiver_is_self_dispatch, resolve_logic_call_targets, LogicNameLookup},
    text_scan::collect_logic_references_from_text,
    LogicRecursionNode,
};

#[derive(Debug, Clone)]
pub(super) struct LogicCallEdge {
    pub(super) caller_idx: usize,
    pub(super) callee_idx: usize,
    pub(super) actual_args: Vec<PureExpr>,
    pub(super) path_conditions: Vec<PureExpr>,
    pub(super) recovered_from_text_only: bool,
    pub(super) unsupported_reason: Option<String>,
    /// Names bound by match-arm patterns, quantifiers and closure parameters
    /// enclosing the call. `Let` binders never appear: their values are
    /// substituted into the scope, so `actual_args` and `path_conditions` never
    /// mention a let-bound name. A caller parameter in this list means the
    /// call's arguments may refer to the binder rather than the parameter.
    pub(super) enclosing_binders: Vec<String>,
}

/// Call edges for the structural checks that compare arguments to parameters
/// by name (identity pass-through, binder shadowing). Match-arm edges carry an
/// `unsupported_reason`, and their arguments keep the binder names verbatim.
pub(super) fn collect_parsed_logic_call_edges(
    nodes: &[LogicRecursionNode],
    lookup: &LogicNameLookup,
) -> Vec<LogicCallEdge> {
    collect_call_edges(nodes, lookup, false)
}

/// Call edges for variant-decrease PROOFS.
///
/// Identical to [`collect_parsed_logic_call_edges`] except under a match arm:
/// every name the arm pattern binds is renamed apart to a fresh
/// `arm$<n>$<name>` (capture-avoiding), so an edge's arguments and path
/// conditions can only mention caller parameters and names that are free —
/// hence universally quantified — in the decrease query. The arm's path
/// conditions are extended ONLY with what reaching the arm literally means:
/// a top-level binding or alias equals the scrutinee, a literal pattern equals
/// the scrutinee, and a constructor pattern applied to a same-named
/// constructor scrutinee binds its sub-patterns to the matching arguments.
/// Nothing is assumed about arms that do not match; an arm whose decrease
/// needs more than these facts stays unproven, and the caller rejects it.
pub(super) fn collect_variant_proof_call_edges(
    nodes: &[LogicRecursionNode],
    lookup: &LogicNameLookup,
) -> Vec<LogicCallEdge> {
    collect_call_edges(nodes, lookup, true)
}

struct EdgeCtx<'a> {
    lookup: &'a LogicNameLookup,
    /// Rename match-arm binders apart and record pattern facts (variant view).
    variant_view: bool,
    fresh_counter: std::cell::Cell<usize>,
}

fn collect_call_edges(
    nodes: &[LogicRecursionNode],
    lookup: &LogicNameLookup,
    variant_view: bool,
) -> Vec<LogicCallEdge> {
    let ctx = EdgeCtx {
        lookup,
        variant_view,
        fresh_counter: std::cell::Cell::new(0),
    };
    let mut edges = Vec::new();
    for (caller_idx, node) in nodes.iter().enumerate() {
        collect_logic_call_edges_from_expr(
            caller_idx,
            &node.name,
            &node.body,
            &[],
            None,
            &ctx,
            &mut edges,
        );
        let mut text_names = HashSet::new();
        collect_logic_references_from_text(&node.body_text, &mut text_names);
        for name in text_names {
            for callee_idx in
                resolve_logic_call_targets(&name, &lookup.full_path_to_idx, &lookup.name_to_indices)
            {
                edges.push(LogicCallEdge {
                    caller_idx,
                    callee_idx,
                    actual_args: Vec::new(),
                    path_conditions: Vec::new(),
                    recovered_from_text_only: true,
                    unsupported_reason: Some(
                        "call edge is only recoverable from text scanning".to_string(),
                    ),
                    enclosing_binders: Vec::new(),
                });
            }
        }
    }
    edges
}

#[allow(clippy::too_many_lines)]
fn collect_logic_call_edges_from_expr(
    caller_idx: usize,
    caller_name: &str,
    expr: &PureExpr,
    path_conditions: &[PureExpr],
    unsupported_reason: Option<&str>,
    ctx: &EdgeCtx<'_>,
    edges: &mut Vec<LogicCallEdge>,
) {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            for callee_idx in resolve_logic_call_targets(
                name,
                &ctx.lookup.full_path_to_idx,
                &ctx.lookup.name_to_indices,
            ) {
                edges.push(LogicCallEdge {
                    caller_idx,
                    callee_idx,
                    actual_args: args.clone(),
                    path_conditions: path_conditions.to_vec(),
                    recovered_from_text_only: false,
                    unsupported_reason: unsupported_reason.map(str::to_string),
                    enclosing_binders: Vec::new(),
                });
            }
            for arg in args {
                collect_logic_call_edges_from_expr(
                    caller_idx,
                    caller_name,
                    arg,
                    path_conditions,
                    unsupported_reason,
                    ctx,
                    edges,
                );
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if receiver_is_self_dispatch(receiver) {
                let mut actual_args = Vec::with_capacity(args.len() + 1);
                actual_args.push((**receiver).clone());
                actual_args.extend(args.iter().cloned());
                let reason = unsupported_reason.unwrap_or(
                    "method-style mutual recursion is not supported in the first SCC slice",
                );
                let mut callee_indices = resolve_logic_call_targets(
                    method,
                    &ctx.lookup.full_path_to_idx,
                    &ctx.lookup.name_to_indices,
                );
                // Fail-closed self-dispatch threading (the `terminates` trio
                // class, see `graph::add_self_named_method_dispatch_edges`):
                // `self.m(...)` inside the logic fn NAMED `m` dispatches back
                // into the caller itself, but short-name resolution returns
                // nothing whenever the trait declaration and impls share the
                // name. Record the caller edge with the real actual-args and
                // path-conditions so the unconditional-self-recursion and
                // variant-decrease checks see the call instead of silently
                // skipping it.
                if method == caller_name && !callee_indices.contains(&caller_idx) {
                    callee_indices.push(caller_idx);
                }
                for callee_idx in callee_indices {
                    edges.push(LogicCallEdge {
                        caller_idx,
                        callee_idx,
                        actual_args: actual_args.clone(),
                        path_conditions: path_conditions.to_vec(),
                        recovered_from_text_only: false,
                        unsupported_reason: Some(reason.to_string()),
                        enclosing_binders: Vec::new(),
                    });
                }
            }
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                receiver,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
            for arg in args {
                collect_logic_call_edges_from_expr(
                    caller_idx,
                    caller_name,
                    arg,
                    path_conditions,
                    unsupported_reason,
                    ctx,
                    edges,
                );
            }
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                cond,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );

            let mut then_path = path_conditions.to_vec();
            then_path.push((**cond).clone());
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                then_expr,
                &then_path,
                unsupported_reason,
                ctx,
                edges,
            );

            let mut else_path = path_conditions.to_vec();
            else_path.push(PureExpr::UnOp(UnOp::Not, Arc::new((**cond).clone())));
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                else_expr,
                &else_path,
                unsupported_reason,
                ctx,
                edges,
            );
        }
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                lhs,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
            let mut rhs_path = path_conditions.to_vec();
            rhs_path.push((**lhs).clone());
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                rhs,
                &rhs_path,
                unsupported_reason,
                ctx,
                edges,
            );
        }
        PureExpr::BinOp(lhs, BinOp::Or, rhs) => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                lhs,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
            let mut rhs_path = path_conditions.to_vec();
            rhs_path.push(PureExpr::UnOp(UnOp::Not, Arc::new((**lhs).clone())));
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                rhs,
                &rhs_path,
                unsupported_reason,
                ctx,
                edges,
            );
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                scrutinee,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
            for arm in arms {
                collect_logic_call_edges_from_pattern(
                    caller_idx,
                    caller_name,
                    &arm.pattern,
                    path_conditions,
                    Some("match-based mutual recursion is not supported"),
                    ctx,
                    edges,
                );
                let mut arm_edges = Vec::new();
                if ctx.variant_view {
                    let mut renames = HashMap::new();
                    for name in arm.pattern.bound_names() {
                        let n = ctx.fresh_counter.get();
                        ctx.fresh_counter.set(n + 1);
                        renames.insert(
                            name.to_string(),
                            PureExpr::Var(format!("arm${n}${name}"), None),
                        );
                    }
                    let mut arm_path = path_conditions.to_vec();
                    pattern_match_facts(&arm.pattern, scrutinee, &renames, ctx, &mut arm_path);
                    let body = arm.body.substitute_capture_avoiding(
                        &renames,
                        &CaptureAvoidingSubstOptions::default(),
                    );
                    collect_logic_call_edges_from_expr(
                        caller_idx,
                        caller_name,
                        &body,
                        &arm_path,
                        unsupported_reason,
                        ctx,
                        &mut arm_edges,
                    );
                } else {
                    collect_logic_call_edges_from_expr(
                        caller_idx,
                        caller_name,
                        &arm.body,
                        path_conditions,
                        Some("match-based mutual recursion is not supported"),
                        ctx,
                        &mut arm_edges,
                    );
                }
                push_under_binders(edges, arm_edges, arm.pattern.bound_names());
            }
        }
        PureExpr::Forall {
            var,
            body,
            triggers,
            ..
        }
        | PureExpr::Exists {
            var,
            body,
            triggers,
            ..
        } => {
            let mut scoped_edges = Vec::new();
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                Some("quantifier-scoped mutual recursion is not supported"),
                ctx,
                &mut scoped_edges,
            );
            for trigger in triggers {
                for expr in trigger {
                    collect_logic_call_edges_from_expr(
                        caller_idx,
                        caller_name,
                        expr,
                        path_conditions,
                        Some("quantifier-trigger mutual recursion is not supported"),
                        ctx,
                        &mut scoped_edges,
                    );
                }
            }
            push_under_binders(edges, scoped_edges, [var.as_str()]);
        }
        PureExpr::Let { var, value, body } => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                value,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
            // Binder-aware: `let x = v; f(x - 1)` calls `f(v - 1)`. Substituting
            // the value (capture-avoiding) keeps every name in the collected
            // arguments and path conditions bound where the edge is USED — the
            // enclosing parameters — so a `let` that shadows a parameter can no
            // longer masquerade as that parameter in a decrease query.
            let mut substitution = HashMap::new();
            substitution.insert(var.clone(), (**value).clone());
            let body = body.substitute_capture_avoiding(
                &substitution,
                &CaptureAvoidingSubstOptions::default(),
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                &body,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                assumption,
                path_conditions,
                Some("LetAssume-scoped mutual recursion is not supported"),
                ctx,
                edges,
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                Some("LetAssume-scoped mutual recursion is not supported"),
                ctx,
                edges,
            );
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                obligation,
                path_conditions,
                Some("LetObligation-scoped mutual recursion is not supported"),
                ctx,
                edges,
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                Some("LetObligation-scoped mutual recursion is not supported"),
                ctx,
                edges,
            );
        }
        PureExpr::Closure { params, body } => {
            let mut scoped_edges = Vec::new();
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                Some("closure-scoped mutual recursion is not supported"),
                ctx,
                &mut scoped_edges,
            );
            push_under_binders(
                edges,
                scoped_edges,
                params.iter().map(|(name, _)| name.as_str()),
            );
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                lhs,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                rhs,
                path_conditions,
                unsupported_reason,
                ctx,
                edges,
            );
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => collect_logic_call_edges_from_expr(
            caller_idx,
            caller_name,
            inner,
            path_conditions,
            unsupported_reason,
            ctx,
            edges,
        ),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        _ => {}
    }
}

/// Append `scoped` to `edges`, recording `binders` as enclosing each edge.
fn push_under_binders<'a>(
    edges: &mut Vec<LogicCallEdge>,
    scoped: Vec<LogicCallEdge>,
    binders: impl IntoIterator<Item = &'a str>,
) {
    let binders: Vec<String> = binders.into_iter().map(str::to_string).collect();
    edges.extend(scoped.into_iter().map(|mut edge| {
        edge.enclosing_binders.extend(binders.iter().cloned());
        edge
    }));
}

fn collect_logic_call_edges_from_pattern(
    caller_idx: usize,
    caller_name: &str,
    pattern: &Pattern,
    path_conditions: &[PureExpr],
    unsupported_reason: Option<&str>,
    ctx: &EdgeCtx<'_>,
    edges: &mut Vec<LogicCallEdge>,
) {
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) => {}
        Pattern::Literal(expr) => collect_logic_call_edges_from_expr(
            caller_idx,
            caller_name,
            expr,
            path_conditions,
            unsupported_reason,
            ctx,
            edges,
        ),
        Pattern::Constructor {
            inner: Some(inner), ..
        } => collect_logic_call_edges_from_pattern(
            caller_idx,
            caller_name,
            inner,
            path_conditions,
            unsupported_reason,
            ctx,
            edges,
        ),
        Pattern::Constructor { inner: None, .. } => {}
        Pattern::Tuple(elements) => {
            for element in elements {
                collect_logic_call_edges_from_pattern(
                    caller_idx,
                    caller_name,
                    element,
                    path_conditions,
                    unsupported_reason,
                    ctx,
                    edges,
                );
            }
        }
        #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
        _ => {}
    }
}

/// Facts that hold whenever `pattern` matched `scrutinee` (variant view only),
/// stated over the renamed binders. Only literal consequences of the match are
/// produced; an unrecognized shape produces nothing (weaker hypotheses).
fn pattern_match_facts(
    pattern: &Pattern,
    scrutinee: &PureExpr,
    renames: &HashMap<String, PureExpr>,
    ctx: &EdgeCtx<'_>,
    out: &mut Vec<PureExpr>,
) {
    let eq = |lhs: PureExpr, rhs: &PureExpr| {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs.clone()))
    };
    match pattern {
        Pattern::Wildcard => {}
        Pattern::Binding(name) => {
            if let Some(fresh) = renames.get(name) {
                out.push(eq(fresh.clone(), scrutinee));
            }
        }
        Pattern::Literal(literal) => {
            if matches!(literal, PureExpr::Int(_) | PureExpr::Bool(_)) {
                out.push(eq(scrutinee.clone(), literal));
            }
        }
        Pattern::Alias { alias, pattern } => {
            if let Some(fresh) = renames.get(alias) {
                out.push(eq(fresh.clone(), scrutinee));
            }
            pattern_match_facts(pattern, scrutinee, renames, ctx, out);
        }
        Pattern::Constructor { name, inner } => {
            // Only a scrutinee that IS a same-named constructor application
            // (and not a logic function of that name) tells us its fields.
            let PureExpr::LogicFnCall {
                name: scrutinee_name,
                args,
            } = scrutinee
            else {
                return;
            };
            if scrutinee_name != name
                || !resolve_logic_call_targets(
                    scrutinee_name,
                    &ctx.lookup.full_path_to_idx,
                    &ctx.lookup.name_to_indices,
                )
                .is_empty()
            {
                return;
            }
            match inner.as_deref() {
                None => {}
                Some(inner) if args.len() == 1 => {
                    pattern_match_facts(inner, &args[0], renames, ctx, out);
                }
                Some(Pattern::Tuple(elements)) if elements.len() == args.len() => {
                    for (element, arg) in elements.iter().zip(args) {
                        pattern_match_facts(element, arg, renames, ctx, out);
                    }
                }
                Some(_) => {}
            }
        }
        // Tuple scrutinees and any future pattern shape: no facts (weaker).
        #[allow(unreachable_patterns)]
        Pattern::Tuple(_) | _ => {}
    }
}
