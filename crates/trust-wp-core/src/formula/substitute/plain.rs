// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Plain and filtered substitution with optional tuple beta-reduction.

use std::sync::Arc;

use super::{
    super::{
        pure_expr::{MatchArm, PureExpr},
        types::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
    },
    overlay::{CaptureAvoidingSubstOptions, ScopedSubstitutions, SubstituteOptions},
    rename::{fresh_var_name, rename_free_var},
    reuse_arc, reuse_expr,
};

/// A binder of `var` over `scope` (a body and its triggers), renamed apart
/// when a substitution value visible beneath it reads a free `var`: that
/// value's `var` is not the bound one, and substituting it under the binder
/// would capture it (`forall<y> y == result` with `result := y` read
/// `forall<y> y == y`). `var` must already be shadowed. `None` when nothing
/// is captured.
fn rename_captured_binder(
    var: &str,
    scope: &[&PureExpr],
    binding: &mut ScopedSubstitutions<'_>,
) -> Option<(String, Vec<PureExpr>)> {
    if !binding.visible_value_mentions_summarizing(var) {
        return None;
    }
    let fresh = fresh_var_name(var, binding, scope, None);
    let options = CaptureAvoidingSubstOptions::default();
    let renamed = scope
        .iter()
        .map(|expr| rename_free_var(expr, var, &fresh, &options))
        .collect();
    Some((fresh, renamed))
}

/// A quantifier's variable, body and triggers, renamed apart when captured.
fn quantifier_parts(
    var: &str,
    body: &Arc<PureExpr>,
    triggers: &[Vec<PureExpr>],
    binding: &mut ScopedSubstitutions<'_>,
) -> Option<(String, PureExpr, Vec<Vec<PureExpr>>)> {
    let mut scope: Vec<&PureExpr> = vec![body.as_ref()];
    scope.extend(triggers.iter().flatten());
    let (fresh, mut renamed) = rename_captured_binder(var, &scope, binding)?;
    let body = renamed.remove(0);
    let mut rest = renamed.into_iter();
    let triggers = triggers
        .iter()
        .map(|group| rest.by_ref().take(group.len()).collect())
        .collect();
    Some((fresh, body, triggers))
}

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
            // Binder-erasing normalisation (#125): `^x [x := <literal>]` is the
            // literal itself when `x` is a bound name being erased — bound
            // values have no temporal state. Only fires for a `Final` DIRECTLY
            // over a substituted, non-shadowed `Var` with a ground-literal
            // replacement; every other shape keeps the `Final` wrapper so the
            // downstream accepting evaluators can refuse it fail-closed.
            if options.binder_erasing {
                if let PureExpr::Var(name, _) = inner.as_ref() {
                    if options.allows_name(name) {
                        if let Some(replacement) = binding.get(name) {
                            if matches!(
                                replacement,
                                PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_)
                            ) {
                                return replacement.clone();
                            }
                        }
                    }
                }
            }
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
        }
        | PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            binding.shadow_name(var);
            let renamed = quantifier_parts(var, body, triggers, binding);
            let (new_var, new_body, new_triggers) = match &renamed {
                Some((fresh, renamed_body, renamed_triggers)) => (
                    fresh.clone(),
                    Arc::new(recurse(renamed_body, binding)),
                    renamed_triggers
                        .iter()
                        .map(|trigger| trigger.iter().map(|e| recurse(e, binding)).collect())
                        .collect(),
                ),
                None => (
                    var.clone(),
                    reuse_arc(body, recurse(body, binding)),
                    triggers
                        .iter()
                        .map(|trigger| trigger.iter().map(|e| recurse(e, binding)).collect())
                        .collect(),
                ),
            };
            binding.unshadow_name(var);
            let node = if matches!(expr, PureExpr::Forall { .. }) {
                PureExpr::Forall {
                    var: new_var,
                    var_sort: var_sort.clone(),
                    body: new_body,
                    triggers: new_triggers,
                }
            } else {
                PureExpr::Exists {
                    var: new_var,
                    var_sort: var_sort.clone(),
                    body: new_body,
                    triggers: new_triggers,
                }
            };
            reuse_expr(expr, node)
        }
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee = recurse(scrutinee, binding);
            let new_arms = arms
                .iter()
                .map(|arm| {
                    let bound = binding.shadow_names(arm.pattern.bound_names());
                    let mut pattern = arm.pattern.clone();
                    let mut arm_body = arm.body.clone();
                    for name in &bound {
                        if let Some((fresh, mut renamed)) =
                            rename_captured_binder(name, &[&arm_body], binding)
                        {
                            arm_body = renamed.remove(0);
                            pattern = pattern.rename_binding(name, &fresh);
                        }
                    }
                    let body = recurse(&arm_body, binding);
                    for name in bound.iter().rev() {
                        binding.unshadow_name(name);
                    }
                    MatchArm { pattern, body }
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
            let (new_var, new_body) = match rename_captured_binder(var, &[body], binding) {
                Some((fresh, mut renamed)) => {
                    let renamed_body = renamed.remove(0);
                    (fresh, Arc::new(recurse(&renamed_body, binding)))
                }
                None => (var.clone(), reuse_arc(body, recurse(body, binding))),
            };
            binding.unshadow_name(var);
            reuse_expr(
                expr,
                PureExpr::Let {
                    var: new_var,
                    value: reuse_arc(value, new_value),
                    body: new_body,
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
            let mut new_params = params.clone();
            let mut closure_body = body.as_ref().clone();
            for (param, _) in &mut new_params {
                if let Some((fresh, mut renamed)) =
                    rename_captured_binder(param, &[&closure_body], binding)
                {
                    closure_body = renamed.remove(0);
                    *param = fresh;
                }
            }
            let new_body = recurse(&closure_body, binding);
            for name in shadowed.iter().rev() {
                binding.unshadow_name(name);
            }
            reuse_expr(
                expr,
                PureExpr::Closure {
                    params: new_params,
                    body: reuse_arc(body, new_body),
                },
            )
        }
    }
}
