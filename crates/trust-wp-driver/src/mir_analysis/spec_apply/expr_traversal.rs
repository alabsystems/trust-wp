// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expression tree traversal utilities for contract spec application.
//!
//! Provides variable replacement (respecting bound-variable shadowing),
//! pattern binding extraction, and free-variable collection over `PureExpr`.

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

#[allow(clippy::too_many_lines)]
pub(super) fn replace_var_allow_bound(
    expr: &PureExpr,
    target: &str,
    replacement: &PureExpr,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, _) if name == target => replacement.clone(),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(_, _) => expr.clone(),
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(replace_var_allow_bound(left, target, replacement)),
            *op,
            Arc::new(replace_var_allow_bound(right, target, replacement)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(replace_var_allow_bound(inner, target, replacement)),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(replace_var_allow_bound(cond, target, replacement)),
            Arc::new(replace_var_allow_bound(then_expr, target, replacement)),
            Arc::new(replace_var_allow_bound(else_expr, target, replacement)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(replace_var_allow_bound(
            inner,
            target,
            replacement,
        ))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(replace_var_allow_bound(
            inner,
            target,
            replacement,
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(replace_var_allow_bound(
            inner,
            target,
            replacement,
        ))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(replace_var_allow_bound(
            inner,
            target,
            replacement,
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(replace_var_allow_bound(receiver, target, replacement)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| replace_var_allow_bound(arg, target, replacement))
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            // Bound variable shadows target — don't substitute inside (#1630)
            if var == target {
                return expr.clone();
            }
            PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(replace_var_allow_bound(body, target, replacement)),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| replace_var_allow_bound(expr, target, replacement))
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            // Exists is intentionally NOT shadowed: the only caller
            // (connect_final_receiver_state_witness) targets the existential
            // witness variable itself, so capture through exists is by design.
            PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(replace_var_allow_bound(body, target, replacement)),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| replace_var_allow_bound(expr, target, replacement))
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(replace_var_allow_bound(scrutinee, target, replacement)),
            arms: arms
                .iter()
                .map(|arm| {
                    // If the arm pattern binds the target variable, don't substitute
                    // in the arm body — the pattern binding shadows it (#1630)
                    let mut bindings = HashSet::new();
                    extract_pattern_bindings(&arm.pattern, &mut bindings);
                    let body = if bindings.contains(target) {
                        arm.body.clone()
                    } else {
                        replace_var_allow_bound(&arm.body, target, replacement)
                    };
                    MatchArm {
                        pattern: arm.pattern.clone(),
                        body,
                    }
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| replace_var_allow_bound(arg, target, replacement))
                .collect(),
        },
        PureExpr::Let { var, value, body } => {
            // Let-bound variable shadows target in the body (not the value) (#1630)
            let new_body = if var == target {
                (**body).clone()
            } else {
                replace_var_allow_bound(body, target, replacement)
            };
            PureExpr::Let {
                var: var.clone(),
                value: Arc::new(replace_var_allow_bound(value, target, replacement)),
                body: Arc::new(new_body),
            }
        }
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(replace_var_allow_bound(assumption, target, replacement)),
            body: Arc::new(replace_var_allow_bound(body, target, replacement)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(replace_var_allow_bound(obligation, target, replacement)),
            body: Arc::new(replace_var_allow_bound(body, target, replacement)),
        },
        PureExpr::Closure { params, body } => {
            // Closure params shadow target — don't substitute in body (#1630)
            let shadows = params.iter().any(|(name, _)| name == target);
            PureExpr::Closure {
                params: params.clone(),
                body: if shadows {
                    body.clone()
                } else {
                    Arc::new(replace_var_allow_bound(body, target, replacement))
                },
            }
        }
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}

pub(super) fn extract_pattern_bindings(pattern: &Pattern, bindings: &mut HashSet<String>) {
    match pattern {
        Pattern::Wildcard | Pattern::Literal(_) => {}
        Pattern::Binding(name) => {
            bindings.insert(name.clone());
        }
        Pattern::Alias { alias, pattern } => {
            bindings.insert(alias.clone());
            extract_pattern_bindings(pattern, bindings);
        }
        Pattern::Constructor {
            inner: Some(inner_pattern),
            ..
        } => {
            extract_pattern_bindings(inner_pattern, bindings);
        }
        Pattern::Constructor { inner: None, .. } => {}
        Pattern::Tuple(elements) => {
            for elem in elements {
                extract_pattern_bindings(elem, bindings);
            }
        }
        // Pattern is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
}
