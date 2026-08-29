// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PureExpr tree walkers for collecting method calls and resolve calls.
//!
//! Provides ground and body-level collection functions for `postcondition_mut`
//! and `resolve()` calls, used by the eager instantiation engine.

use std::collections::HashSet;

use trust_wp_core::formula::PureExpr;

use super::MethodCallPattern;
use crate::encoder::MAX_ENCODING_DEPTH;

#[derive(Clone, Copy)]
struct BinderTraversalPolicy {
    include_quantifier_triggers: bool,
    descend_into_resolve_args: bool,
}

const BODY_POSTCONDITION_MUT_POLICY: BinderTraversalPolicy = BinderTraversalPolicy {
    include_quantifier_triggers: true,
    descend_into_resolve_args: true,
};

const BODY_RESOLVE_POLICY: BinderTraversalPolicy = BinderTraversalPolicy {
    include_quantifier_triggers: false,
    descend_into_resolve_args: false,
};

const GROUND_POSTCONDITION_MUT_POLICY: BinderTraversalPolicy = BinderTraversalPolicy {
    include_quantifier_triggers: false,
    descend_into_resolve_args: true,
};

const GROUND_RESOLVE_POLICY: BinderTraversalPolicy = BinderTraversalPolicy {
    include_quantifier_triggers: false,
    descend_into_resolve_args: false,
};

/// Collect postcondition_mut method calls from the existential body.
pub(in crate::verify) fn collect_body_postcondition_mut_calls<'a>(
    expr: &'a PureExpr,
    bound_vars: &[String],
) -> Vec<MethodCallPattern<'a>> {
    let mut calls = Vec::new();
    let outer_bound_vars: HashSet<String> = bound_vars.iter().cloned().collect();
    let mut active_binders = Vec::new();
    walk_expr_with_active_binders(
        expr,
        0,
        BODY_POSTCONDITION_MUT_POLICY,
        &mut |node, active_binders| {
            let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = node
            else {
                return;
            };
            if method != "postcondition_mut" {
                return;
            }
            if !method_call_mentions_shadowed_bound_var(
                receiver,
                args,
                &outer_bound_vars,
                active_binders,
            ) {
                calls.push(MethodCallPattern { receiver, args });
            }
        },
        &mut active_binders,
    );
    calls
}

fn method_call_mentions_shadowed_bound_var(
    receiver: &PureExpr,
    args: &[PureExpr],
    outer_bound_vars: &HashSet<String>,
    active_binders: &[String],
) -> bool {
    let shadowed: HashSet<&str> = active_binders
        .iter()
        .map(String::as_str)
        .filter(|name| outer_bound_vars.contains(*name))
        .collect();
    if shadowed.is_empty() {
        return false;
    }
    receiver.any_free_var(|name, _sort| shadowed.contains(name))
        || args
            .iter()
            .any(|arg| arg.any_free_var(|name, _sort| shadowed.contains(name)))
}

/// Collect ground postcondition_mut calls from preconditions.
pub(crate) fn collect_ground_postcondition_mut_calls(
    requires: &[PureExpr],
) -> Vec<MethodCallPattern<'_>> {
    collect_ground_postcondition_mut_calls_iter(requires.iter())
}

/// Collect ground postcondition_mut calls from body-local `LetAssume`
/// assumptions. Body assumptions (e.g., from sequential `f()` calls in a
/// function whose contract uses `exists<st1, st2, r>`) carry the ground
/// witnesses the existential needs, but the existing precondition-only
/// collector misses them. Reusing the same walker keeps the binder-aware
/// filtering identical for both call sites. (#970)
pub(crate) fn collect_ground_postcondition_mut_calls_from_refs<'a>(
    assumptions: &[&'a PureExpr],
) -> Vec<MethodCallPattern<'a>> {
    collect_ground_postcondition_mut_calls_iter(assumptions.iter().copied())
}

fn collect_ground_postcondition_mut_calls_iter<'a, I>(exprs: I) -> Vec<MethodCallPattern<'a>>
where
    I: IntoIterator<Item = &'a PureExpr>,
{
    let mut calls = Vec::new();
    for req in exprs {
        let mut active_binders = Vec::new();
        walk_expr_with_active_binders(
            req,
            0,
            GROUND_POSTCONDITION_MUT_POLICY,
            &mut |node, active_binders| {
                let PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } = node
                else {
                    return;
                };
                if method != "postcondition_mut" {
                    return;
                }
                let mentions_quantified =
                    super::matching::expr_mentions_bound_var(receiver, active_binders)
                        || args.iter().any(|arg| {
                            super::matching::expr_mentions_bound_var(arg, active_binders)
                        });
                if !mentions_quantified {
                    calls.push(MethodCallPattern { receiver, args });
                }
            },
            &mut active_binders,
        );
    }
    calls
}

/// Collect resolve() LogicFnCall args from the body that reference bound vars.
pub(in crate::verify) fn collect_body_resolve_calls<'a>(
    expr: &'a PureExpr,
    bound_vars: &[String],
) -> Vec<&'a PureExpr> {
    let mut calls = Vec::new();
    let outer_bound_vars: HashSet<String> = bound_vars.iter().cloned().collect();
    let mut active_binders = Vec::new();
    walk_expr_with_active_binders(
        expr,
        0,
        BODY_RESOLVE_POLICY,
        &mut |node, active_binders| {
            let PureExpr::LogicFnCall { name, args } = node else {
                return;
            };
            if name == "resolve"
                && args.len() == 1
                && expr_mentions_visible_outer_var(&args[0], &outer_bound_vars, active_binders)
            {
                calls.push(&args[0]);
            }
        },
        &mut active_binders,
    );
    calls
}

/// Collect ground resolve() calls from preconditions.
pub(crate) fn collect_ground_resolve_calls(requires: &[PureExpr]) -> Vec<&PureExpr> {
    collect_ground_resolve_calls_iter(requires.iter())
}

/// Collect ground resolve() calls from body-local `LetAssume` assumptions.
/// Companion to `collect_ground_postcondition_mut_calls_from_refs` for the
/// resolve-binding extension step. (#970)
pub(crate) fn collect_ground_resolve_calls_from_refs<'a>(
    assumptions: &[&'a PureExpr],
) -> Vec<&'a PureExpr> {
    collect_ground_resolve_calls_iter(assumptions.iter().copied())
}

fn collect_ground_resolve_calls_iter<'a, I>(exprs: I) -> Vec<&'a PureExpr>
where
    I: IntoIterator<Item = &'a PureExpr>,
{
    let mut calls = Vec::new();
    for req in exprs {
        let mut active_binders = Vec::new();
        walk_expr_with_active_binders(
            req,
            0,
            GROUND_RESOLVE_POLICY,
            &mut |node, active_binders| {
                let PureExpr::LogicFnCall { name, args } = node else {
                    return;
                };
                if name == "resolve"
                    && args.len() == 1
                    && !super::matching::expr_mentions_bound_var(&args[0], active_binders)
                {
                    calls.push(&args[0]);
                }
            },
            &mut active_binders,
        );
    }
    calls
}

fn expr_mentions_visible_outer_var(
    expr: &PureExpr,
    outer_bound_vars: &HashSet<String>,
    active_binders: &[String],
) -> bool {
    let shadowed: HashSet<&str> = active_binders
        .iter()
        .map(String::as_str)
        .filter(|name| outer_bound_vars.contains(*name))
        .collect();
    expr.any_free_var(|name, _sort| outer_bound_vars.contains(name) && !shadowed.contains(name))
}

fn walk_expr_with_active_binders<'a, F>(
    expr: &'a PureExpr,
    depth: usize,
    policy: BinderTraversalPolicy,
    visit: &mut F,
    active_binders: &mut Vec<String>,
) where
    F: FnMut(&'a PureExpr, &[String]),
{
    if depth > MAX_ENCODING_DEPTH {
        return;
    }
    visit(expr, active_binders);
    let next = depth + 1;
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            if !policy.descend_into_resolve_args && name == "resolve" && args.len() == 1 {
                return;
            }
            for arg in args {
                walk_expr_with_active_binders(arg, next, policy, visit, active_binders);
            }
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            walk_expr_with_active_binders(receiver, next, policy, visit, active_binders);
            for arg in args {
                walk_expr_with_active_binders(arg, next, policy, visit, active_binders);
            }
        }
        PureExpr::BinOp(l, _, r) => {
            walk_expr_with_active_binders(l, next, policy, visit, active_binders);
            walk_expr_with_active_binders(r, next, policy, visit, active_binders);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            walk_expr_with_active_binders(inner, next, policy, visit, active_binders);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            walk_expr_with_active_binders(cond, next, policy, visit, active_binders);
            walk_expr_with_active_binders(then_expr, next, policy, visit, active_binders);
            walk_expr_with_active_binders(else_expr, next, policy, visit, active_binders);
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
            active_binders.push(var.clone());
            walk_expr_with_active_binders(body, next, policy, visit, active_binders);
            if policy.include_quantifier_triggers {
                for trigger in triggers.iter().flat_map(|trigger| trigger.iter()) {
                    walk_expr_with_active_binders(trigger, next, policy, visit, active_binders);
                }
            }
            active_binders.pop();
        }
        PureExpr::Match { scrutinee, arms } => {
            walk_expr_with_active_binders(scrutinee, next, policy, visit, active_binders);
            for arm in arms {
                let binders = arm
                    .pattern
                    .bound_names()
                    .into_iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                let base_len = active_binders.len();
                active_binders.extend(binders);
                walk_expr_with_active_binders(&arm.body, next, policy, visit, active_binders);
                active_binders.truncate(base_len);
            }
        }
        PureExpr::Let { var, value, body } => {
            walk_expr_with_active_binders(value, next, policy, visit, active_binders);
            let base_len = active_binders.len();
            active_binders.push(var.clone());
            walk_expr_with_active_binders(body, next, policy, visit, active_binders);
            active_binders.truncate(base_len);
        }
        PureExpr::LetAssume { assumption, body } => {
            walk_expr_with_active_binders(assumption, next, policy, visit, active_binders);
            walk_expr_with_active_binders(body, next, policy, visit, active_binders);
        }
        PureExpr::LetObligation { obligation, body } => {
            walk_expr_with_active_binders(obligation, next, policy, visit, active_binders);
            walk_expr_with_active_binders(body, next, policy, visit, active_binders);
        }
        PureExpr::Closure { params, body } => {
            let base_len = active_binders.len();
            active_binders.extend(params.iter().map(|(param, _)| param.clone()));
            walk_expr_with_active_binders(body, next, policy, visit, active_binders);
            active_binders.truncate(base_len);
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(..) => {}
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
}
