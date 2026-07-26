// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Depth-limited `PureExpr` traversal helpers.
//!
//! `PureExpr` already owns the unbounded recursive walkers in `pure_expr.rs`.
//! This extension trait adds the ay-facing depth-limited variants used by
//! verification code that must fail closed or preserve too-deep subtrees.

use super::{
    pure_expr::{reuse_arc, reuse_node},
    MatchArm, PureExpr,
};

fn any_recursive_with_depth_limit_inner<F>(
    expr: &PureExpr,
    pred: &mut F,
    depth: usize,
    depth_limit: usize,
    on_limit: bool,
) -> bool
where
    F: FnMut(&PureExpr) -> bool,
{
    if depth > depth_limit {
        return on_limit;
    }
    if pred(expr) {
        return true;
    }

    let next = depth + 1;
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        PureExpr::BinOp(left, _, right) => {
            any_recursive_with_depth_limit_inner(left, pred, next, depth_limit, on_limit)
                || any_recursive_with_depth_limit_inner(right, pred, next, depth_limit, on_limit)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            any_recursive_with_depth_limit_inner(inner, pred, next, depth_limit, on_limit)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            any_recursive_with_depth_limit_inner(cond, pred, next, depth_limit, on_limit)
                || any_recursive_with_depth_limit_inner(
                    then_expr,
                    pred,
                    next,
                    depth_limit,
                    on_limit,
                )
                || any_recursive_with_depth_limit_inner(
                    else_expr,
                    pred,
                    next,
                    depth_limit,
                    on_limit,
                )
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            any_recursive_with_depth_limit_inner(receiver, pred, next, depth_limit, on_limit)
                || args.iter().any(|arg| {
                    any_recursive_with_depth_limit_inner(arg, pred, next, depth_limit, on_limit)
                })
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            any_recursive_with_depth_limit_inner(body, pred, next, depth_limit, on_limit)
                || triggers
                    .iter()
                    .flat_map(|trigger| trigger.iter())
                    .any(|expr| {
                        any_recursive_with_depth_limit_inner(
                            expr,
                            pred,
                            next,
                            depth_limit,
                            on_limit,
                        )
                    })
        }
        PureExpr::Match { scrutinee, arms } => {
            any_recursive_with_depth_limit_inner(scrutinee, pred, next, depth_limit, on_limit)
                || arms.iter().any(|arm| {
                    any_recursive_with_depth_limit_inner(
                        &arm.body,
                        pred,
                        next,
                        depth_limit,
                        on_limit,
                    )
                })
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(|arg| {
            any_recursive_with_depth_limit_inner(arg, pred, next, depth_limit, on_limit)
        }),
        PureExpr::Let { value, body, .. } => {
            any_recursive_with_depth_limit_inner(value, pred, next, depth_limit, on_limit)
                || any_recursive_with_depth_limit_inner(body, pred, next, depth_limit, on_limit)
        }
        PureExpr::LetAssume { assumption, body } => {
            any_recursive_with_depth_limit_inner(assumption, pred, next, depth_limit, on_limit)
                || any_recursive_with_depth_limit_inner(body, pred, next, depth_limit, on_limit)
        }
        PureExpr::LetObligation { obligation, body } => {
            any_recursive_with_depth_limit_inner(obligation, pred, next, depth_limit, on_limit)
                || any_recursive_with_depth_limit_inner(body, pred, next, depth_limit, on_limit)
        }
        PureExpr::Closure { body, .. } => {
            any_recursive_with_depth_limit_inner(body, pred, next, depth_limit, on_limit)
        }
    }
}

fn for_each_recursive_with_depth_limit_inner<'a, F>(
    expr: &'a PureExpr,
    visit: &mut F,
    depth: usize,
    depth_limit: usize,
) where
    F: FnMut(&'a PureExpr),
{
    if depth > depth_limit {
        return;
    }

    visit(expr);

    let next = depth + 1;
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        PureExpr::BinOp(left, _, right) => {
            for_each_recursive_with_depth_limit_inner(left, visit, next, depth_limit);
            for_each_recursive_with_depth_limit_inner(right, visit, next, depth_limit);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            for_each_recursive_with_depth_limit_inner(inner, visit, next, depth_limit);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            for_each_recursive_with_depth_limit_inner(cond, visit, next, depth_limit);
            for_each_recursive_with_depth_limit_inner(then_expr, visit, next, depth_limit);
            for_each_recursive_with_depth_limit_inner(else_expr, visit, next, depth_limit);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            for_each_recursive_with_depth_limit_inner(receiver, visit, next, depth_limit);
            for arg in args {
                for_each_recursive_with_depth_limit_inner(arg, visit, next, depth_limit);
            }
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            for_each_recursive_with_depth_limit_inner(body, visit, next, depth_limit);
            for expr in triggers.iter().flat_map(|trigger| trigger.iter()) {
                for_each_recursive_with_depth_limit_inner(expr, visit, next, depth_limit);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            for_each_recursive_with_depth_limit_inner(scrutinee, visit, next, depth_limit);
            for arm in arms {
                for_each_recursive_with_depth_limit_inner(&arm.body, visit, next, depth_limit);
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                for_each_recursive_with_depth_limit_inner(arg, visit, next, depth_limit);
            }
        }
        PureExpr::Let { value, body, .. } => {
            for_each_recursive_with_depth_limit_inner(value, visit, next, depth_limit);
            for_each_recursive_with_depth_limit_inner(body, visit, next, depth_limit);
        }
        PureExpr::LetAssume { assumption, body } => {
            for_each_recursive_with_depth_limit_inner(assumption, visit, next, depth_limit);
            for_each_recursive_with_depth_limit_inner(body, visit, next, depth_limit);
        }
        PureExpr::LetObligation { obligation, body } => {
            for_each_recursive_with_depth_limit_inner(obligation, visit, next, depth_limit);
            for_each_recursive_with_depth_limit_inner(body, visit, next, depth_limit);
        }
        PureExpr::Closure { body, .. } => {
            for_each_recursive_with_depth_limit_inner(body, visit, next, depth_limit);
        }
    }
}

fn any_recursive_binding_aware_with_depth_limit_inner<F>(
    expr: &PureExpr,
    var: &str,
    pred: &mut F,
    depth: usize,
    depth_limit: usize,
    on_limit: bool,
) -> bool
where
    F: FnMut(&PureExpr) -> bool,
{
    if depth > depth_limit {
        return on_limit;
    }
    if pred(expr) {
        return true;
    }

    let next = depth + 1;
    let mut r = |e: &PureExpr| {
        any_recursive_binding_aware_with_depth_limit_inner(
            e,
            var,
            pred,
            next,
            depth_limit,
            on_limit,
        )
    };
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        PureExpr::BinOp(left, _, right) => r(left) || r(right),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => r(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => r(cond) || r(then_expr) || r(else_expr),
        PureExpr::MethodCall { receiver, args, .. } => r(receiver) || args.iter().any(&mut r),
        PureExpr::Forall {
            var: bound,
            body,
            triggers,
            ..
        }
        | PureExpr::Exists {
            var: bound,
            body,
            triggers,
            ..
        } => {
            // Triggers are outside binding scope — always visit.
            let trigger_hit = triggers
                .iter()
                .flat_map(|trigger| trigger.iter())
                .any(&mut r);
            if trigger_hit {
                return true;
            }
            bound != var && r(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            r(scrutinee)
                || arms
                    .iter()
                    .any(|arm| !arm.pattern.binds_name(var) && r(&arm.body))
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(&mut r),
        PureExpr::Let {
            var: bound,
            value,
            body,
        } => r(value) || (bound != var && r(body)),
        PureExpr::LetAssume { assumption, body } => r(assumption) || r(body),
        PureExpr::LetObligation { obligation, body } => r(obligation) || r(body),
        PureExpr::Closure { params, body } => {
            !params.iter().any(|(name, _)| name == var) && r(body)
        }
    }
}

#[allow(clippy::too_many_lines)]
fn rewrite_bottom_up_with_depth_limit_inner<F>(
    expr: &PureExpr,
    rewrite: &mut F,
    depth: usize,
    depth_limit: usize,
) -> PureExpr
where
    F: FnMut(PureExpr) -> PureExpr,
{
    if depth > depth_limit {
        return expr.clone();
    }

    let next = depth + 1;
    let rebuilt = match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
            expr.clone()
        }
        PureExpr::BinOp(left, op, right) => {
            let new_left =
                rewrite_bottom_up_with_depth_limit_inner(left, rewrite, next, depth_limit);
            let new_right =
                rewrite_bottom_up_with_depth_limit_inner(right, rewrite, next, depth_limit);
            reuse_node(
                expr,
                PureExpr::BinOp(reuse_arc(left, new_left), *op, reuse_arc(right, new_right)),
            )
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner =
                rewrite_bottom_up_with_depth_limit_inner(inner, rewrite, next, depth_limit);
            reuse_node(expr, PureExpr::UnOp(*op, reuse_arc(inner, new_inner)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let new_cond =
                rewrite_bottom_up_with_depth_limit_inner(cond, rewrite, next, depth_limit);
            let new_then =
                rewrite_bottom_up_with_depth_limit_inner(then_expr, rewrite, next, depth_limit);
            let new_else =
                rewrite_bottom_up_with_depth_limit_inner(else_expr, rewrite, next, depth_limit);
            reuse_node(
                expr,
                PureExpr::Ite(
                    reuse_arc(cond, new_cond),
                    reuse_arc(then_expr, new_then),
                    reuse_arc(else_expr, new_else),
                ),
            )
        }
        PureExpr::Old(inner) => {
            let new_inner =
                rewrite_bottom_up_with_depth_limit_inner(inner, rewrite, next, depth_limit);
            reuse_node(expr, PureExpr::Old(reuse_arc(inner, new_inner)))
        }
        PureExpr::Deref(inner) => {
            let new_inner =
                rewrite_bottom_up_with_depth_limit_inner(inner, rewrite, next, depth_limit);
            reuse_node(expr, PureExpr::Deref(reuse_arc(inner, new_inner)))
        }
        PureExpr::Final(inner) => {
            let new_inner =
                rewrite_bottom_up_with_depth_limit_inner(inner, rewrite, next, depth_limit);
            reuse_node(expr, PureExpr::Final(reuse_arc(inner, new_inner)))
        }
        PureExpr::View(inner) => {
            let new_inner =
                rewrite_bottom_up_with_depth_limit_inner(inner, rewrite, next, depth_limit);
            reuse_node(expr, PureExpr::View(reuse_arc(inner, new_inner)))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver =
                rewrite_bottom_up_with_depth_limit_inner(receiver, rewrite, next, depth_limit);
            let new_args = args
                .iter()
                .map(|arg| {
                    rewrite_bottom_up_with_depth_limit_inner(arg, rewrite, next, depth_limit)
                })
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
            let new_body =
                rewrite_bottom_up_with_depth_limit_inner(body, rewrite, next, depth_limit);
            let new_triggers = triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|expr| {
                            rewrite_bottom_up_with_depth_limit_inner(
                                expr,
                                rewrite,
                                next,
                                depth_limit,
                            )
                        })
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
            let new_body =
                rewrite_bottom_up_with_depth_limit_inner(body, rewrite, next, depth_limit);
            let new_triggers = triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|expr| {
                            rewrite_bottom_up_with_depth_limit_inner(
                                expr,
                                rewrite,
                                next,
                                depth_limit,
                            )
                        })
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
            let new_scrutinee =
                rewrite_bottom_up_with_depth_limit_inner(scrutinee, rewrite, next, depth_limit);
            let new_arms = arms
                .iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern.clone(),
                    body: rewrite_bottom_up_with_depth_limit_inner(
                        &arm.body,
                        rewrite,
                        next,
                        depth_limit,
                    ),
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
            let new_args = args
                .iter()
                .map(|arg| {
                    rewrite_bottom_up_with_depth_limit_inner(arg, rewrite, next, depth_limit)
                })
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
            let new_value =
                rewrite_bottom_up_with_depth_limit_inner(value, rewrite, next, depth_limit);
            let new_body =
                rewrite_bottom_up_with_depth_limit_inner(body, rewrite, next, depth_limit);
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
            let new_assumption =
                rewrite_bottom_up_with_depth_limit_inner(assumption, rewrite, next, depth_limit);
            let new_body =
                rewrite_bottom_up_with_depth_limit_inner(body, rewrite, next, depth_limit);
            reuse_node(
                expr,
                PureExpr::LetAssume {
                    assumption: reuse_arc(assumption, new_assumption),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            let new_obligation =
                rewrite_bottom_up_with_depth_limit_inner(obligation, rewrite, next, depth_limit);
            let new_body =
                rewrite_bottom_up_with_depth_limit_inner(body, rewrite, next, depth_limit);
            reuse_node(
                expr,
                PureExpr::LetObligation {
                    obligation: reuse_arc(obligation, new_obligation),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Closure { params, body } => {
            let new_body =
                rewrite_bottom_up_with_depth_limit_inner(body, rewrite, next, depth_limit);
            reuse_node(
                expr,
                PureExpr::Closure {
                    params: params.clone(),
                    body: reuse_arc(body, new_body),
                },
            )
        }
    };

    rewrite(rebuilt)
}

/// Depth-limited traversal helpers for `PureExpr`.
pub trait PureExprDepthLimitedTraversalExt {
    /// Return true if any node in this expression tree matches `pred`.
    ///
    /// When recursion would descend beyond `depth_limit`, return `on_limit`
    /// instead of visiting deeper nodes.
    fn any_recursive_with_depth_limit<F>(
        &self,
        depth_limit: usize,
        on_limit: bool,
        pred: F,
    ) -> bool
    where
        F: FnMut(&PureExpr) -> bool;

    /// Binding-aware depth-limited search: return true if any node (where `var`
    /// is free) matches `pred`. Skips subtrees where `var` is shadowed by a
    /// binder (`Forall`, `Exists`, `Let`, `Closure`, `Match` pattern bindings).
    ///
    /// When recursion would descend beyond `depth_limit`, return `on_limit`.
    fn any_recursive_binding_aware_with_depth_limit<F>(
        &self,
        var: &str,
        depth_limit: usize,
        on_limit: bool,
        pred: F,
    ) -> bool
    where
        F: FnMut(&PureExpr) -> bool;

    /// Visit each node in this expression tree in depth-first pre-order while
    /// skipping any subtree beyond `depth_limit`.
    fn for_each_recursive_with_depth_limit<'a, F>(&'a self, depth_limit: usize, visit: F)
    where
        F: FnMut(&'a PureExpr);

    /// Rebuild this expression bottom-up while preserving any subtree beyond
    /// `depth_limit` unchanged.
    #[must_use]
    fn rewrite_bottom_up_with_depth_limit<F>(&self, depth_limit: usize, rewrite: F) -> PureExpr
    where
        F: FnMut(PureExpr) -> PureExpr;
}

impl PureExprDepthLimitedTraversalExt for PureExpr {
    fn any_recursive_with_depth_limit<F>(
        &self,
        depth_limit: usize,
        on_limit: bool,
        mut pred: F,
    ) -> bool
    where
        F: FnMut(&PureExpr) -> bool,
    {
        any_recursive_with_depth_limit_inner(self, &mut pred, 0, depth_limit, on_limit)
    }

    fn any_recursive_binding_aware_with_depth_limit<F>(
        &self,
        var: &str,
        depth_limit: usize,
        on_limit: bool,
        mut pred: F,
    ) -> bool
    where
        F: FnMut(&PureExpr) -> bool,
    {
        any_recursive_binding_aware_with_depth_limit_inner(
            self,
            var,
            &mut pred,
            0,
            depth_limit,
            on_limit,
        )
    }

    fn for_each_recursive_with_depth_limit<'a, F>(&'a self, depth_limit: usize, mut visit: F)
    where
        F: FnMut(&'a PureExpr),
    {
        for_each_recursive_with_depth_limit_inner(self, &mut visit, 0, depth_limit);
    }

    fn rewrite_bottom_up_with_depth_limit<F>(&self, depth_limit: usize, mut rewrite: F) -> PureExpr
    where
        F: FnMut(PureExpr) -> PureExpr,
    {
        rewrite_bottom_up_with_depth_limit_inner(self, &mut rewrite, 0, depth_limit)
    }
}
