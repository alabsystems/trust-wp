// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Free-occurrence checking, fresh variable generation, and alpha-renaming.

use std::sync::Arc;

use super::{
    super::pure_expr::{MatchArm, PureExpr},
    depth_limit_exceeded,
    overlay::{CaptureAvoidingSubstOptions, ScopedSubstitutions},
    reuse_arc, reuse_expr,
};

/// Check whether `name` appears free anywhere in `expr`.
///
/// This is used by capture-avoiding substitution to detect when a binder would
/// capture a free variable from a substitution value.
#[doc(hidden)]
#[must_use]
pub fn expr_has_free_occurrence(
    expr: &PureExpr,
    name: &str,
    options: &CaptureAvoidingSubstOptions,
) -> bool {
    expr_has_free_occurrence_inner(expr, name, 0, options.depth_limit)
}

pub(super) fn expr_has_free_occurrence_inner(
    expr: &PureExpr,
    name: &str,
    depth: usize,
    depth_limit: Option<usize>,
) -> bool {
    if depth_limit_exceeded(depth, depth_limit) {
        return true;
    }
    let next = depth + 1;
    match expr {
        PureExpr::Var(var_name, _) => var_name == name,
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
        PureExpr::BinOp(left, _, right) => {
            expr_has_free_occurrence_inner(left, name, next, depth_limit)
                || expr_has_free_occurrence_inner(right, name, next, depth_limit)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner) => expr_has_free_occurrence_inner(inner, name, next, depth_limit),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_has_free_occurrence_inner(cond, name, next, depth_limit)
                || expr_has_free_occurrence_inner(then_expr, name, next, depth_limit)
                || expr_has_free_occurrence_inner(else_expr, name, next, depth_limit)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_has_free_occurrence_inner(receiver, name, next, depth_limit)
                || args
                    .iter()
                    .any(|arg| expr_has_free_occurrence_inner(arg, name, next, depth_limit))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| expr_has_free_occurrence_inner(arg, name, next, depth_limit)),
        PureExpr::Forall { var, body, .. } | PureExpr::Exists { var, body, .. } => {
            if var == name {
                return false;
            }
            expr_has_free_occurrence_inner(body, name, next, depth_limit)
        }
        PureExpr::Let { var, value, body } => {
            expr_has_free_occurrence_inner(value, name, next, depth_limit)
                || (var != name && expr_has_free_occurrence_inner(body, name, next, depth_limit))
        }
        PureExpr::Match { scrutinee, arms } => {
            expr_has_free_occurrence_inner(scrutinee, name, next, depth_limit)
                || arms.iter().any(|arm| {
                    !arm.pattern.binds_name(name)
                        && expr_has_free_occurrence_inner(&arm.body, name, next, depth_limit)
                })
        }
        PureExpr::LetAssume { assumption, body }
        | PureExpr::LetObligation {
            obligation: assumption,
            body,
        } => {
            expr_has_free_occurrence_inner(assumption, name, next, depth_limit)
                || expr_has_free_occurrence_inner(body, name, next, depth_limit)
        }
        PureExpr::Closure { params, body } => {
            if params.iter().any(|(param, _)| param == name) {
                return false;
            }
            expr_has_free_occurrence_inner(body, name, next, depth_limit)
        }
    }
}

pub(super) fn fresh_var_name(
    base: &str,
    binding: &ScopedSubstitutions<'_>,
    avoid_in: &[&PureExpr],
    depth_limit: Option<usize>,
) -> String {
    for index in 0u32.. {
        let candidate = format!("{base}$\u{03b1}{index}");
        if !binding.contains_key(&candidate)
            && !binding.visible_value_mentions(&candidate, depth_limit)
            && !avoid_in
                .iter()
                .any(|expr| expr_has_free_occurrence_inner(expr, &candidate, 0, depth_limit))
        {
            return candidate;
        }
    }
    unreachable!("fresh variable generation is unbounded");
}

/// Rename all free occurrences of `old_name` to `new_name`.
#[doc(hidden)]
#[must_use]
pub fn rename_free_var(
    expr: &PureExpr,
    old_name: &str,
    new_name: &str,
    options: &CaptureAvoidingSubstOptions,
) -> PureExpr {
    rename_free_var_inner(expr, old_name, new_name, 0, options.depth_limit)
}

#[allow(clippy::too_many_lines)]
pub(super) fn rename_free_var_inner(
    expr: &PureExpr,
    old_name: &str,
    new_name: &str,
    depth: usize,
    depth_limit: Option<usize>,
) -> PureExpr {
    if depth_limit_exceeded(depth, depth_limit) {
        return expr.clone();
    }
    let next = depth + 1;
    let rename =
        |inner: &PureExpr| rename_free_var_inner(inner, old_name, new_name, next, depth_limit);
    match expr {
        PureExpr::Var(var_name, sort) if var_name == old_name => {
            PureExpr::Var(new_name.to_string(), sort.clone())
        }
        PureExpr::BinOp(left, op, right) => {
            let new_left = rename(left);
            let new_right = rename(right);
            reuse_expr(
                expr,
                PureExpr::BinOp(reuse_arc(left, new_left), *op, reuse_arc(right, new_right)),
            )
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = rename(inner);
            reuse_expr(expr, PureExpr::UnOp(*op, reuse_arc(inner, new_inner)))
        }
        PureExpr::Deref(inner) => {
            let new_inner = rename(inner);
            reuse_expr(expr, PureExpr::Deref(reuse_arc(inner, new_inner)))
        }
        PureExpr::Final(inner) => {
            let new_inner = rename(inner);
            reuse_expr(expr, PureExpr::Final(reuse_arc(inner, new_inner)))
        }
        PureExpr::View(inner) => {
            let new_inner = rename(inner);
            reuse_expr(expr, PureExpr::View(reuse_arc(inner, new_inner)))
        }
        PureExpr::Old(inner) => {
            let new_inner = rename(inner);
            reuse_expr(expr, PureExpr::Old(reuse_arc(inner, new_inner)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let new_cond = rename(cond);
            let new_then = rename(then_expr);
            let new_else = rename(else_expr);
            reuse_expr(
                expr,
                PureExpr::Ite(
                    reuse_arc(cond, new_cond),
                    reuse_arc(then_expr, new_then),
                    reuse_arc(else_expr, new_else),
                ),
            )
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = rename(receiver);
            let new_args = args.iter().map(rename).collect();
            reuse_expr(
                expr,
                PureExpr::MethodCall {
                    receiver: reuse_arc(receiver, new_receiver),
                    method: method.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args = args.iter().map(rename).collect();
            reuse_expr(
                expr,
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } if var != old_name => {
            let new_body = rename(body);
            let new_triggers = triggers
                .iter()
                .map(|trigger| trigger.iter().map(rename).collect())
                .collect();
            reuse_expr(
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
        } if var != old_name => {
            let new_body = rename(body);
            let new_triggers = triggers
                .iter()
                .map(|trigger| trigger.iter().map(rename).collect())
                .collect();
            reuse_expr(
                expr,
                PureExpr::Exists {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: reuse_arc(body, new_body),
                    triggers: new_triggers,
                },
            )
        }
        PureExpr::Let { var, value, body } if var != old_name => {
            let new_value = rename(value);
            let new_body = rename(body);
            reuse_expr(
                expr,
                PureExpr::Let {
                    var: var.clone(),
                    value: reuse_arc(value, new_value),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Let { var, value, body } => {
            let new_value = rename(value);
            reuse_expr(
                expr,
                PureExpr::Let {
                    var: var.clone(),
                    value: reuse_arc(value, new_value),
                    body: Arc::clone(body),
                },
            )
        }
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee = rename(scrutinee);
            let new_arms = arms
                .iter()
                .map(|arm| {
                    if arm.pattern.binds_name(old_name) {
                        arm.clone()
                    } else {
                        MatchArm {
                            pattern: arm.pattern.clone(),
                            body: rename(&arm.body),
                        }
                    }
                })
                .collect();
            reuse_expr(
                expr,
                PureExpr::Match {
                    scrutinee: reuse_arc(scrutinee, new_scrutinee),
                    arms: new_arms,
                },
            )
        }
        PureExpr::LetAssume { assumption, body } => {
            let new_assumption = rename(assumption);
            let new_body = rename(body);
            reuse_expr(
                expr,
                PureExpr::LetAssume {
                    assumption: reuse_arc(assumption, new_assumption),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            let new_obligation = rename(obligation);
            let new_body = rename(body);
            reuse_expr(
                expr,
                PureExpr::LetObligation {
                    obligation: reuse_arc(obligation, new_obligation),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Closure { params, body }
            if !params.iter().any(|(param, _)| param == old_name) =>
        {
            let new_body = rename(body);
            reuse_expr(
                expr,
                PureExpr::Closure {
                    params: params.clone(),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Var(..)
        | PureExpr::Bool(_)
        | PureExpr::Int(_)
        | PureExpr::Float(_)
        | PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Closure { .. } => expr.clone(),
    }
}

impl PureExpr {
    /// This expression with every binder (`forall`, `exists`, `let`, a
    /// `match` arm's pattern, a closure parameter) of a name `apart` accepts
    /// renamed to a fresh name, with the occurrences it binds. A pass that
    /// reads a name as a program variable (a parameter's sort, a `&mut`
    /// parameter's final value) then cannot reach a binder that shadows it.
    #[must_use]
    pub fn rename_binders_apart(&self, apart: impl Fn(&str) -> bool) -> PureExpr {
        let options = CaptureAvoidingSubstOptions::default();
        let mut counter = 0usize;
        let mut fresh = |name: &str, scope: &[&PureExpr]| loop {
            let candidate = format!("{name}$b{counter}");
            counter += 1;
            if !scope
                .iter()
                .any(|expr| expr_has_free_occurrence(expr, &candidate, &options))
            {
                return candidate;
            }
        };
        self.rewrite_bottom_up(|node| match node {
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } if apart(&var) => {
                let (var, body, triggers) =
                    rename_quantifier(&var, &body, &triggers, &mut fresh, &options);
                PureExpr::Forall {
                    var,
                    var_sort,
                    body,
                    triggers,
                }
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } if apart(&var) => {
                let (var, body, triggers) =
                    rename_quantifier(&var, &body, &triggers, &mut fresh, &options);
                PureExpr::Exists {
                    var,
                    var_sort,
                    body,
                    triggers,
                }
            }
            PureExpr::Let { var, value, body } if apart(&var) => {
                let renamed = fresh(&var, &[&body]);
                PureExpr::Let {
                    body: Arc::new(rename_free_var(&body, &var, &renamed, &options)),
                    var: renamed,
                    value,
                }
            }
            PureExpr::Match { scrutinee, arms }
                if arms
                    .iter()
                    .any(|arm| arm.pattern.bound_names().into_iter().any(&apart)) =>
            {
                PureExpr::Match {
                    scrutinee,
                    arms: arms
                        .into_iter()
                        .map(|arm| {
                            let mut pattern = arm.pattern.clone();
                            let mut body = arm.body;
                            for name in arm.pattern.bound_names() {
                                if apart(name) {
                                    let renamed = fresh(name, &[&body]);
                                    body = rename_free_var(&body, name, &renamed, &options);
                                    pattern = pattern.rename_binding(name, &renamed);
                                }
                            }
                            MatchArm { pattern, body }
                        })
                        .collect(),
                }
            }
            PureExpr::Closure { mut params, body }
                if params.iter().any(|(param, _)| apart(param)) =>
            {
                let mut body = body.as_ref().clone();
                for (param, _) in &mut params {
                    if apart(param) {
                        let renamed = fresh(param, &[&body]);
                        body = rename_free_var(&body, param, &renamed, &options);
                        *param = renamed;
                    }
                }
                PureExpr::Closure {
                    params,
                    body: Arc::new(body),
                }
            }
            node => node,
        })
    }
}

fn rename_quantifier(
    var: &str,
    body: &PureExpr,
    triggers: &[Vec<PureExpr>],
    fresh: &mut impl FnMut(&str, &[&PureExpr]) -> String,
    options: &CaptureAvoidingSubstOptions,
) -> (String, Arc<PureExpr>, Vec<Vec<PureExpr>>) {
    let mut scope: Vec<&PureExpr> = vec![body];
    scope.extend(triggers.iter().flatten());
    let renamed = fresh(var, &scope);
    let body = Arc::new(rename_free_var(body, var, &renamed, options));
    let triggers = triggers
        .iter()
        .map(|group| {
            group
                .iter()
                .map(|expr| rename_free_var(expr, var, &renamed, options))
                .collect()
        })
        .collect();
    (renamed, body, triggers)
}
