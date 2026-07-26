// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Plain and filtered substitution with optional tuple beta-reduction.

use super::{
    super::{
        pure_expr::{MatchArm, PureExpr},
        types::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
    },
    overlay::{ScopedSubstitutions, SubstituteOptions},
    reuse_arc, reuse_expr,
};

#[allow(clippy::too_many_lines)]
pub(super) fn substitute_with_options_inner(
    expr: &PureExpr,
    binding: &mut ScopedSubstitutions<'_>,
    options: SubstituteOptions<'_>,
) -> PureExpr {
    let recurse = |e: &PureExpr, b: &mut ScopedSubstitutions<'_>| {
        substitute_with_options_inner(e, b, options)
    };
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => expr.clone(),
        PureExpr::Var(name, sort) => {
            if options.allows_name(name) {
                if let Some(replacement) = binding.get(name) {
                    return replacement.clone();
                }
            }
            PureExpr::Var(name.clone(), sort.clone())
        }
        PureExpr::BinOp(left, op, right) => {
            let new_left = recurse(left, binding);
            let new_right = recurse(right, binding);
            reuse_expr(
                expr,
                PureExpr::BinOp(reuse_arc(left, new_left), *op, reuse_arc(right, new_right)),
            )
        }
        PureExpr::UnOp(op, operand) => {
            let new_operand = recurse(operand, binding);
            reuse_expr(expr, PureExpr::UnOp(*op, reuse_arc(operand, new_operand)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let new_cond = recurse(cond, binding);
            let new_then = recurse(then_expr, binding);
            let new_else = recurse(else_expr, binding);
            reuse_expr(
                expr,
                PureExpr::Ite(
                    reuse_arc(cond, new_cond),
                    reuse_arc(then_expr, new_then),
                    reuse_arc(else_expr, new_else),
                ),
            )
        }
        PureExpr::Old(inner) => {
            let new_inner = recurse(inner, binding);
            reuse_expr(expr, PureExpr::Old(reuse_arc(inner, new_inner)))
        }
        PureExpr::Deref(inner) => {
            // Deref-key lookup: `*name` keys are synthetic and are NOT shadowed
            // when `name` is shadowed. This preserves existing semantics where
            // `forall x. *x` still resolves the `*x` substitution entry.
            if let PureExpr::Var(name, _) = inner.as_ref() {
                if options.allows_name(name) {
                    let deref_key = format!("*{name}");
                    if let Some(replacement) = binding.get(&deref_key) {
                        return replacement.clone();
                    }
                }
            }
            let new_inner = recurse(inner, binding);
            reuse_expr(expr, PureExpr::Deref(reuse_arc(inner, new_inner)))
        }
        PureExpr::Final(inner) => {
            let new_inner = recurse(inner, binding);
            reuse_expr(expr, PureExpr::Final(reuse_arc(inner, new_inner)))
        }
        PureExpr::View(inner) => {
            let new_inner = recurse(inner, binding);
            reuse_expr(expr, PureExpr::View(reuse_arc(inner, new_inner)))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = recurse(receiver, binding);
            let new_args = args.iter().map(|arg| recurse(arg, binding)).collect();
            reuse_expr(
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
            binding.shadow_name(var);
            let new_body = recurse(body, binding);
            let new_triggers = triggers
                .iter()
                .map(|trigger| trigger.iter().map(|e| recurse(e, binding)).collect())
                .collect();
            binding.unshadow_name(var);
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
        } => {
            binding.shadow_name(var);
            let new_body = recurse(body, binding);
            let new_triggers = triggers
                .iter()
                .map(|trigger| trigger.iter().map(|e| recurse(e, binding)).collect())
                .collect();
            binding.unshadow_name(var);
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
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee = recurse(scrutinee, binding);
            let new_arms = arms
                .iter()
                .map(|arm| {
                    let bound = binding.shadow_names(arm.pattern.bound_names());
                    let body = recurse(&arm.body, binding);
                    for name in bound.iter().rev() {
                        binding.unshadow_name(name);
                    }
                    MatchArm {
                        pattern: arm.pattern.clone(),
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
        PureExpr::LogicFnCall { name, args } => {
            let substituted_args: Vec<PureExpr> =
                args.iter().map(|arg| recurse(arg, binding)).collect();
            if substituted_args.is_empty() && options.allows_name(name) {
                if let Some(replacement) = binding.get(name) {
                    return replacement.clone();
                }
            }
            if options.beta_reduce_tuples {
                if let Some(field_idx) = tuple_field_logic_fn_index(name) {
                    if substituted_args.len() == 1 {
                        if let PureExpr::LogicFnCall {
                            name: ref ctor_name,
                            args: ref ctor_args,
                        } = substituted_args[0]
                        {
                            if let Some(arity) = tuple_logic_fn_arity(ctor_name) {
                                if arity == ctor_args.len() && field_idx < ctor_args.len() {
                                    return ctor_args[field_idx].clone();
                                }
                            }
                        }
                    }
                }
            }
            reuse_expr(
                expr,
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: substituted_args,
                },
            )
        }
        PureExpr::Let { var, value, body } => {
            let new_value = recurse(value, binding);
            binding.shadow_name(var);
            let new_body = recurse(body, binding);
            binding.unshadow_name(var);
            reuse_expr(
                expr,
                PureExpr::Let {
                    var: var.clone(),
                    value: reuse_arc(value, new_value),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetAssume { assumption, body } => {
            let new_assumption = recurse(assumption, binding);
            let new_body = recurse(body, binding);
            reuse_expr(
                expr,
                PureExpr::LetAssume {
                    assumption: reuse_arc(assumption, new_assumption),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            let new_obligation = recurse(obligation, binding);
            let new_body = recurse(body, binding);
            reuse_expr(
                expr,
                PureExpr::LetObligation {
                    obligation: reuse_arc(obligation, new_obligation),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Closure { params, body } => {
            let shadowed = binding.shadow_names(params.iter().map(|(name, _)| name.as_str()));
            let new_body = recurse(body, binding);
            for name in shadowed.iter().rev() {
                binding.unshadow_name(name);
            }
            reuse_expr(
                expr,
                PureExpr::Closure {
                    params: params.clone(),
                    body: reuse_arc(body, new_body),
                },
            )
        }
    }
}
