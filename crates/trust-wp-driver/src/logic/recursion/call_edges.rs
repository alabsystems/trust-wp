// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parsed call-edge collection from logic function expressions.
//!
//! Walks `PureExpr` trees to extract structured call edges with actual arguments
//! and path conditions, used by variant-decrease proofs for mutual recursion.

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{BinOp, Pattern, PureExpr, UnOp};

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
}

pub(super) fn collect_parsed_logic_call_edges(
    nodes: &[LogicRecursionNode],
    lookup: &LogicNameLookup,
) -> Vec<LogicCallEdge> {
    let mut edges = Vec::new();
    for (caller_idx, node) in nodes.iter().enumerate() {
        collect_logic_call_edges_from_expr(
            caller_idx,
            &node.name,
            &node.body,
            &[],
            None,
            lookup,
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
    lookup: &LogicNameLookup,
    edges: &mut Vec<LogicCallEdge>,
) {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            for callee_idx in
                resolve_logic_call_targets(name, &lookup.full_path_to_idx, &lookup.name_to_indices)
            {
                edges.push(LogicCallEdge {
                    caller_idx,
                    callee_idx,
                    actual_args: args.clone(),
                    path_conditions: path_conditions.to_vec(),
                    recovered_from_text_only: false,
                    unsupported_reason: unsupported_reason.map(str::to_string),
                });
            }
            for arg in args {
                collect_logic_call_edges_from_expr(
                    caller_idx,
                    caller_name,
                    arg,
                    path_conditions,
                    unsupported_reason,
                    lookup,
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
                    &lookup.full_path_to_idx,
                    &lookup.name_to_indices,
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
                    });
                }
            }
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                receiver,
                path_conditions,
                unsupported_reason,
                lookup,
                edges,
            );
            for arg in args {
                collect_logic_call_edges_from_expr(
                    caller_idx,
                    caller_name,
                    arg,
                    path_conditions,
                    unsupported_reason,
                    lookup,
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
                lookup,
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
                lookup,
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
                lookup,
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
                lookup,
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
                lookup,
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
                lookup,
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
                lookup,
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
                lookup,
                edges,
            );
            for arm in arms {
                collect_logic_call_edges_from_pattern(
                    caller_idx,
                    caller_name,
                    &arm.pattern,
                    path_conditions,
                    Some("match-based mutual recursion is not supported"),
                    lookup,
                    edges,
                );
                collect_logic_call_edges_from_expr(
                    caller_idx,
                    caller_name,
                    &arm.body,
                    path_conditions,
                    Some("match-based mutual recursion is not supported"),
                    lookup,
                    edges,
                );
            }
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                Some("quantifier-scoped mutual recursion is not supported"),
                lookup,
                edges,
            );
            for trigger in triggers {
                for expr in trigger {
                    collect_logic_call_edges_from_expr(
                        caller_idx,
                        caller_name,
                        expr,
                        path_conditions,
                        Some("quantifier-trigger mutual recursion is not supported"),
                        lookup,
                        edges,
                    );
                }
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                value,
                path_conditions,
                unsupported_reason,
                lookup,
                edges,
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                unsupported_reason,
                lookup,
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
                lookup,
                edges,
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                Some("LetAssume-scoped mutual recursion is not supported"),
                lookup,
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
                lookup,
                edges,
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                body,
                path_conditions,
                Some("LetObligation-scoped mutual recursion is not supported"),
                lookup,
                edges,
            );
        }
        PureExpr::Closure { body, .. } => collect_logic_call_edges_from_expr(
            caller_idx,
            caller_name,
            body,
            path_conditions,
            Some("closure-scoped mutual recursion is not supported"),
            lookup,
            edges,
        ),
        PureExpr::BinOp(lhs, _, rhs) => {
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                lhs,
                path_conditions,
                unsupported_reason,
                lookup,
                edges,
            );
            collect_logic_call_edges_from_expr(
                caller_idx,
                caller_name,
                rhs,
                path_conditions,
                unsupported_reason,
                lookup,
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
            lookup,
            edges,
        ),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        _ => {}
    }
}

fn collect_logic_call_edges_from_pattern(
    caller_idx: usize,
    caller_name: &str,
    pattern: &Pattern,
    path_conditions: &[PureExpr],
    unsupported_reason: Option<&str>,
    lookup: &LogicNameLookup,
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
            lookup,
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
            lookup,
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
                    lookup,
                    edges,
                );
            }
        }
        #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
        _ => {}
    }
}
