// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Capture-avoiding substitution engine.

use std::sync::Arc;

use super::{
    super::pure_expr::{ExprSort, MatchArm, PureExpr},
    depth_limit_exceeded,
    overlay::{CaptureAvoidingSubstOptions, ScopedSubstitutions},
    rename::{fresh_var_name, rename_free_var},
    reuse_arc, reuse_expr,
};

fn substitute_quantifier_parts(
    var: &str,
    body: &PureExpr,
    triggers: &[Vec<PureExpr>],
    binding: &mut ScopedSubstitutions<'_>,
    depth: usize,
    depth_limit: Option<usize>,
) -> (String, Arc<PureExpr>, Vec<Vec<PureExpr>>) {
    binding.shadow_name(var);
    let captures = binding.visible_value_mentions(var, depth_limit);
    let capture_options = CaptureAvoidingSubstOptions { depth_limit };
    let (effective_var, effective_body, effective_triggers) = if captures {
        let mut avoid_in: Vec<&PureExpr> = vec![body];
        avoid_in.extend(triggers.iter().flat_map(|trigger| trigger.iter()));
        let fresh = fresh_var_name(var, binding, &avoid_in, depth_limit);
        let renamed_body = rename_free_var(body, var, &fresh, &capture_options);
        let renamed_triggers = triggers
            .iter()
            .map(|trigger| {
                trigger
                    .iter()
                    .map(|expr| rename_free_var(expr, var, &fresh, &capture_options))
                    .collect()
            })
            .collect();
        (fresh, renamed_body, renamed_triggers)
    } else {
        (var.to_string(), body.clone(), triggers.to_vec())
    };
    let new_body = Arc::new(substitute_capture_avoiding_inner(
        &effective_body,
        binding,
        depth,
        depth_limit,
    ));
    let new_triggers = effective_triggers
        .iter()
        .map(|trigger| {
            trigger
                .iter()
                .map(|expr| substitute_capture_avoiding_inner(expr, binding, depth, depth_limit))
                .collect()
        })
        .collect();
    binding.unshadow_name(var);
    (effective_var, new_body, new_triggers)
}

fn substitute_let_capture_avoiding(
    var: &str,
    value: &PureExpr,
    body: &PureExpr,
    binding: &mut ScopedSubstitutions<'_>,
    depth: usize,
    depth_limit: Option<usize>,
) -> PureExpr {
    let new_value = Arc::new(substitute_capture_avoiding_inner(
        value,
        binding,
        depth,
        depth_limit,
    ));
    binding.shadow_name(var);
    let capture_options = CaptureAvoidingSubstOptions { depth_limit };
    let result = if binding.visible_value_mentions(var, depth_limit) {
        let fresh = fresh_var_name(var, binding, &[body], depth_limit);
        let renamed_body = rename_free_var(body, var, &fresh, &capture_options);
        PureExpr::Let {
            var: fresh,
            value: new_value,
            body: Arc::new(substitute_capture_avoiding_inner(
                &renamed_body,
                binding,
                depth,
                depth_limit,
            )),
        }
    } else {
        PureExpr::Let {
            var: var.to_string(),
            value: new_value,
            body: Arc::new(substitute_capture_avoiding_inner(
                body,
                binding,
                depth,
                depth_limit,
            )),
        }
    };
    binding.unshadow_name(var);
    result
}

fn substitute_closure_capture_avoiding(
    params: &[(String, Option<ExprSort>)],
    body: &PureExpr,
    binding: &mut ScopedSubstitutions<'_>,
    depth: usize,
    depth_limit: Option<usize>,
) -> PureExpr {
    let shadowed_params = binding.shadow_names(params.iter().map(|(param, _)| param.as_str()));
    let capture_options = CaptureAvoidingSubstOptions { depth_limit };
    let mut effective_params = params.to_vec();
    let mut effective_body = body.clone();
    for (param, _) in &mut effective_params {
        if binding.visible_value_mentions(param, depth_limit) {
            let fresh = fresh_var_name(param, binding, &[&effective_body], depth_limit);
            effective_body = rename_free_var(&effective_body, param, &fresh, &capture_options);
            *param = fresh;
        }
    }
    let result = PureExpr::Closure {
        params: effective_params,
        body: Arc::new(substitute_capture_avoiding_inner(
            &effective_body,
            binding,
            depth,
            depth_limit,
        )),
    };
    for param in shadowed_params.iter().rev() {
        binding.unshadow_name(param);
    }
    result
}

#[allow(clippy::too_many_lines)]
pub(super) fn substitute_capture_avoiding_inner(
    expr: &PureExpr,
    binding: &mut ScopedSubstitutions<'_>,
    depth: usize,
    depth_limit: Option<usize>,
) -> PureExpr {
    if depth_limit_exceeded(depth, depth_limit) {
        return expr.clone();
    }
    let next = depth + 1;
    match expr {
        PureExpr::Var(name, _) => binding.get(name).cloned().unwrap_or_else(|| expr.clone()),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => expr.clone(),
        PureExpr::BinOp(left, op, right) => {
            let new_left = substitute_capture_avoiding_inner(left, binding, next, depth_limit);
            let new_right = substitute_capture_avoiding_inner(right, binding, next, depth_limit);
            reuse_expr(
                expr,
                PureExpr::BinOp(reuse_arc(left, new_left), *op, reuse_arc(right, new_right)),
            )
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = substitute_capture_avoiding_inner(inner, binding, next, depth_limit);
            reuse_expr(expr, PureExpr::UnOp(*op, reuse_arc(inner, new_inner)))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver =
                substitute_capture_avoiding_inner(receiver, binding, next, depth_limit);
            let new_args = args
                .iter()
                .map(|arg| substitute_capture_avoiding_inner(arg, binding, next, depth_limit))
                .collect();
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
            let new_args = args
                .iter()
                .map(|arg| substitute_capture_avoiding_inner(arg, binding, next, depth_limit))
                .collect();
            reuse_expr(
                expr,
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::Deref(inner) => {
            let new_inner = substitute_capture_avoiding_inner(inner, binding, next, depth_limit);
            reuse_expr(expr, PureExpr::Deref(reuse_arc(inner, new_inner)))
        }
        PureExpr::Final(inner) => {
            let new_inner = substitute_capture_avoiding_inner(inner, binding, next, depth_limit);
            reuse_expr(expr, PureExpr::Final(reuse_arc(inner, new_inner)))
        }
        PureExpr::View(inner) => {
            let new_inner = substitute_capture_avoiding_inner(inner, binding, next, depth_limit);
            reuse_expr(expr, PureExpr::View(reuse_arc(inner, new_inner)))
        }
        PureExpr::Old(inner) => {
            let new_inner = substitute_capture_avoiding_inner(inner, binding, next, depth_limit);
            reuse_expr(expr, PureExpr::Old(reuse_arc(inner, new_inner)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let new_cond = substitute_capture_avoiding_inner(cond, binding, next, depth_limit);
            let new_then = substitute_capture_avoiding_inner(then_expr, binding, next, depth_limit);
            let new_else = substitute_capture_avoiding_inner(else_expr, binding, next, depth_limit);
            reuse_expr(
                expr,
                PureExpr::Ite(
                    reuse_arc(cond, new_cond),
                    reuse_arc(then_expr, new_then),
                    reuse_arc(else_expr, new_else),
                ),
            )
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let (new_var, new_body, new_triggers) =
                substitute_quantifier_parts(var, body, triggers, binding, next, depth_limit);
            reuse_expr(
                expr,
                PureExpr::Forall {
                    var: new_var,
                    var_sort: var_sort.clone(),
                    body: new_body,
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
            let (new_var, new_body, new_triggers) =
                substitute_quantifier_parts(var, body, triggers, binding, next, depth_limit);
            reuse_expr(
                expr,
                PureExpr::Exists {
                    var: new_var,
                    var_sort: var_sort.clone(),
                    body: new_body,
                    triggers: new_triggers,
                },
            )
        }
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee =
                substitute_capture_avoiding_inner(scrutinee, binding, next, depth_limit);
            let capture_options = CaptureAvoidingSubstOptions { depth_limit };
            let new_arms = arms
                .iter()
                .map(|arm| {
                    let shadowed_bindings = binding.shadow_names(arm.pattern.bound_names());
                    let mut effective_pattern = arm.pattern.clone();
                    let mut effective_body = arm.body.clone();
                    for bound_name in &shadowed_bindings {
                        if binding.visible_value_mentions(bound_name, depth_limit) {
                            let fresh = fresh_var_name(
                                bound_name,
                                binding,
                                &[&effective_body],
                                depth_limit,
                            );
                            effective_body = rename_free_var(
                                &effective_body,
                                bound_name,
                                &fresh,
                                &capture_options,
                            );
                            effective_pattern =
                                effective_pattern.rename_binding(bound_name, &fresh);
                        }
                    }
                    let body = substitute_capture_avoiding_inner(
                        &effective_body,
                        binding,
                        next,
                        depth_limit,
                    );
                    for bound_name in shadowed_bindings.iter().rev() {
                        binding.unshadow_name(bound_name);
                    }
                    MatchArm {
                        pattern: effective_pattern,
                        body,
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
        PureExpr::Let { var, value, body } => reuse_expr(
            expr,
            substitute_let_capture_avoiding(var, value, body, binding, next, depth_limit),
        ),
        PureExpr::LetAssume { assumption, body } => {
            let new_assumption =
                substitute_capture_avoiding_inner(assumption, binding, next, depth_limit);
            let new_body = substitute_capture_avoiding_inner(body, binding, next, depth_limit);
            reuse_expr(
                expr,
                PureExpr::LetAssume {
                    assumption: reuse_arc(assumption, new_assumption),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            let new_obligation =
                substitute_capture_avoiding_inner(obligation, binding, next, depth_limit);
            let new_body = substitute_capture_avoiding_inner(body, binding, next, depth_limit);
            reuse_expr(
                expr,
                PureExpr::LetObligation {
                    obligation: reuse_arc(obligation, new_obligation),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Closure { params, body } => reuse_expr(
            expr,
            substitute_closure_capture_avoiding(params, body, binding, next, depth_limit),
        ),
    }
}
