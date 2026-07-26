// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared `inside_old`-aware traversal for postcondition transforms.
//!
//! Both the mut-ref rewrite and the closure-capture rewrite need to know
//! whether the current node sits under an `Old(...)` expression. This module
//! provides a single generic tree walk that threads `inside_old` and lets
//! callers supply node-local rewrite or visit callbacks.

use super::super::pure_expr::{reuse_arc, reuse_node, MatchArm, PureExpr};

/// Rewrite a `PureExpr` tree while tracking `inside_old` context.
///
/// At each node, `rewrite` is called first. If it returns `Some(expr)`, that
/// result replaces the node without further recursion. If it returns `None`,
/// the default recursive descent continues.
///
/// `Old(inner)` sets `inside_old = true` for the subtree.
#[allow(clippy::too_many_lines)]
pub(super) fn rewrite_with_old_context(
    expr: &PureExpr,
    inside_old: bool,
    rewrite: &mut impl FnMut(&PureExpr, bool) -> Option<PureExpr>,
) -> PureExpr {
    if let Some(result) = rewrite(expr, inside_old) {
        return result;
    }

    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
            expr.clone()
        }
        PureExpr::BinOp(l, op, r) => {
            let new_l = rewrite_with_old_context(l, inside_old, rewrite);
            let new_r = rewrite_with_old_context(r, inside_old, rewrite);
            reuse_node(
                expr,
                PureExpr::BinOp(reuse_arc(l, new_l), *op, reuse_arc(r, new_r)),
            )
        }
        PureExpr::UnOp(op, operand) => {
            let new_operand = rewrite_with_old_context(operand, inside_old, rewrite);
            reuse_node(expr, PureExpr::UnOp(*op, reuse_arc(operand, new_operand)))
        }
        PureExpr::Ite(c, t, e) => {
            let new_c = rewrite_with_old_context(c, inside_old, rewrite);
            let new_t = rewrite_with_old_context(t, inside_old, rewrite);
            let new_e = rewrite_with_old_context(e, inside_old, rewrite);
            reuse_node(
                expr,
                PureExpr::Ite(
                    reuse_arc(c, new_c),
                    reuse_arc(t, new_t),
                    reuse_arc(e, new_e),
                ),
            )
        }
        PureExpr::Old(inner) => {
            let new_inner = rewrite_with_old_context(inner, true, rewrite);
            reuse_node(expr, PureExpr::Old(reuse_arc(inner, new_inner)))
        }
        PureExpr::Deref(inner) => {
            let new_inner = rewrite_with_old_context(inner, inside_old, rewrite);
            reuse_node(expr, PureExpr::Deref(reuse_arc(inner, new_inner)))
        }
        PureExpr::Final(inner) => {
            let new_inner = rewrite_with_old_context(inner, inside_old, rewrite);
            reuse_node(expr, PureExpr::Final(reuse_arc(inner, new_inner)))
        }
        PureExpr::View(inner) => {
            let new_inner = rewrite_with_old_context(inner, inside_old, rewrite);
            reuse_node(expr, PureExpr::View(reuse_arc(inner, new_inner)))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = rewrite_with_old_context(receiver, inside_old, rewrite);
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| rewrite_with_old_context(a, inside_old, rewrite))
                .collect();
            reuse_node(
                expr,
                PureExpr::MethodCall {
                    receiver: reuse_arc(receiver, new_receiver),
                    method: method.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_body = rewrite_with_old_context(body, inside_old, rewrite);
            let new_triggers: Vec<Vec<PureExpr>> = triggers
                .iter()
                .map(|t| {
                    t.iter()
                        .map(|e| rewrite_with_old_context(e, inside_old, rewrite))
                        .collect()
                })
                .collect();
            reuse_node(
                expr,
                PureExpr::Forall {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: reuse_arc(body, new_body),
                    triggers: new_triggers,
                },
            )
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_body = rewrite_with_old_context(body, inside_old, rewrite);
            let new_triggers: Vec<Vec<PureExpr>> = triggers
                .iter()
                .map(|t| {
                    t.iter()
                        .map(|e| rewrite_with_old_context(e, inside_old, rewrite))
                        .collect()
                })
                .collect();
            reuse_node(
                expr,
                PureExpr::Exists {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: reuse_arc(body, new_body),
                    triggers: new_triggers,
                },
            )
        }
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee = rewrite_with_old_context(scrutinee, inside_old, rewrite);
            let new_arms: Vec<MatchArm> = arms
                .iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern.clone(),
                    body: rewrite_with_old_context(&arm.body, inside_old, rewrite),
                })
                .collect();
            reuse_node(
                expr,
                PureExpr::Match {
                    scrutinee: reuse_arc(scrutinee, new_scrutinee),
                    arms: new_arms,
                },
            )
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| rewrite_with_old_context(a, inside_old, rewrite))
                .collect();
            reuse_node(
                expr,
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::Let { var, value, body } => {
            let new_value = rewrite_with_old_context(value, inside_old, rewrite);
            let new_body = rewrite_with_old_context(body, inside_old, rewrite);
            reuse_node(
                expr,
                PureExpr::Let {
                    var: var.clone(),
                    value: reuse_arc(value, new_value),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetAssume { assumption, body } => {
            let new_assumption = rewrite_with_old_context(assumption, inside_old, rewrite);
            let new_body = rewrite_with_old_context(body, inside_old, rewrite);
            reuse_node(
                expr,
                PureExpr::LetAssume {
                    assumption: reuse_arc(assumption, new_assumption),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            let new_obligation = rewrite_with_old_context(obligation, inside_old, rewrite);
            let new_body = rewrite_with_old_context(body, inside_old, rewrite);
            reuse_node(
                expr,
                PureExpr::LetObligation {
                    obligation: reuse_arc(obligation, new_obligation),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Closure { params, body } => {
            let new_body = rewrite_with_old_context(body, inside_old, rewrite);
            reuse_node(
                expr,
                PureExpr::Closure {
                    params: params.clone(),
                    body: reuse_arc(body, new_body),
                },
            )
        }
    }
}

/// Visit a `PureExpr` tree while tracking `inside_old` context.
///
/// At each node, `visit` is called. `Old(inner)` sets `inside_old = true`
/// for the subtree. This is used for pre-scans like collecting explicit
/// `Final(Var(x))` nodes.
pub(super) fn visit_with_old_context(
    expr: &PureExpr,
    inside_old: bool,
    visit: &mut impl FnMut(&PureExpr, bool),
) {
    visit(expr, inside_old);

    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        PureExpr::BinOp(l, _, r) => {
            visit_with_old_context(l, inside_old, visit);
            visit_with_old_context(r, inside_old, visit);
        }
        PureExpr::UnOp(_, operand) | PureExpr::Deref(operand) | PureExpr::View(operand) => {
            visit_with_old_context(operand, inside_old, visit);
        }
        PureExpr::Ite(c, t, e) => {
            visit_with_old_context(c, inside_old, visit);
            visit_with_old_context(t, inside_old, visit);
            visit_with_old_context(e, inside_old, visit);
        }
        PureExpr::Old(inner) => {
            visit_with_old_context(inner, true, visit);
        }
        PureExpr::Final(inner) => {
            visit_with_old_context(inner, inside_old, visit);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            visit_with_old_context(receiver, inside_old, visit);
            for arg in args {
                visit_with_old_context(arg, inside_old, visit);
            }
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            visit_with_old_context(body, inside_old, visit);
            for trigger_group in triggers {
                for trigger in trigger_group {
                    visit_with_old_context(trigger, inside_old, visit);
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            visit_with_old_context(scrutinee, inside_old, visit);
            for arm in arms {
                visit_with_old_context(&arm.body, inside_old, visit);
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                visit_with_old_context(arg, inside_old, visit);
            }
        }
        PureExpr::Let { value, body, .. } => {
            visit_with_old_context(value, inside_old, visit);
            visit_with_old_context(body, inside_old, visit);
        }
        PureExpr::LetAssume { assumption, body } => {
            visit_with_old_context(assumption, inside_old, visit);
            visit_with_old_context(body, inside_old, visit);
        }
        PureExpr::LetObligation { obligation, body } => {
            visit_with_old_context(obligation, inside_old, visit);
            visit_with_old_context(body, inside_old, visit);
        }
        PureExpr::Closure { body, .. } => {
            visit_with_old_context(body, inside_old, visit);
        }
    }
}
