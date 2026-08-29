// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Old(...)` rewrite for loop postconditions (#2095).
//!
//! Resolves `old(expr)` in loop postconditions by stripping `Old` for stable
//! parameters (those not reassigned before loop entry and not modified by the
//! loop body). Rejects unstable or non-parameter `Old` uses fail-closed.

use std::sync::Arc;

use trust_wp_core::formula::PureExpr;

use super::expr_utils::expr_referenced_vars;

/// Rewrite `Old(...)` expressions in loop postconditions (#2095).
///
/// For loop postconditions, `old(expr)` means the value at function entry.
/// The loop VC operates over loop-exit state, so `Old(...)` must be resolved
/// before encoding. This function:
///
/// 1. Preserves `Old(Deref(...))` — the existing mutable-borrow entry-state form.
/// 2. For other `Old(inner)`, strips `Old` if every free variable in `inner` is
///    a function parameter that was not written before loop entry and not modified
///    by the loop body (stable parameters equal their function-entry value).
/// 3. Rejects `Old(inner)` that references unstable or non-parameter variables.
pub(in crate::callbacks) fn rewrite_loop_postcondition_old(
    ensures: &[PureExpr],
    arg_names: &[String],
    mut_ref_params: &std::collections::HashSet<String>,
    pre_loop_written_params: &std::collections::HashSet<String>,
    modified_vars: &[String],
) -> Result<Vec<PureExpr>, trust_wp_ay::EncodingError> {
    let arg_set: std::collections::HashSet<&str> = arg_names.iter().map(String::as_str).collect();
    let modified_set: std::collections::HashSet<&str> =
        modified_vars.iter().map(String::as_str).collect();
    ensures
        .iter()
        .map(|e| {
            rewrite_old_in_expr(
                e,
                &arg_set,
                mut_ref_params,
                pre_loop_written_params,
                &modified_set,
            )
        })
        .collect()
}

fn rewrite_old_in_expr(
    expr: &PureExpr,
    arg_names: &std::collections::HashSet<&str>,
    mut_ref_params: &std::collections::HashSet<String>,
    pre_loop_written_params: &std::collections::HashSet<String>,
    modified_vars: &std::collections::HashSet<&str>,
) -> Result<PureExpr, trust_wp_ay::EncodingError> {
    match expr {
        PureExpr::Old(inner) => {
            // Preserve Old(Deref(...)) for mutable-borrow entry-state form.
            if let PureExpr::Deref(deref_inner) = inner.as_ref() {
                if let PureExpr::Var(name, _) = deref_inner.as_ref() {
                    if mut_ref_params.contains(name) {
                        return Ok(expr.clone());
                    }
                }
            }
            // Validate that all free variables in `inner` are stable parameters.
            let free_vars = expr_referenced_vars(inner);
            for var in &free_vars {
                if !arg_names.contains(var.as_str()) {
                    return Err(trust_wp_ay::EncodingError::Unsupported {
                        message: format!(
                            "old({var}) in loop postcondition: `{var}` is not a function parameter"
                        ),
                        span: None,
                        contract_text: None,
                    });
                }
                if pre_loop_written_params.contains(var) {
                    return Err(trust_wp_ay::EncodingError::Unsupported {
                        message: format!(
                            "old({var}) in loop postcondition: parameter `{var}` is reassigned before loop entry"
                        ),
                        span: None,
                        contract_text: None,
                    });
                }
                if modified_vars.contains(var.as_str()) {
                    return Err(trust_wp_ay::EncodingError::Unsupported {
                        message: format!(
                            "old({var}) in loop postcondition: parameter `{var}` is modified by the loop body"
                        ),
                        span: None,
                        contract_text: None,
                    });
                }
            }
            // All free variables are stable parameters — strip Old and recurse.
            rewrite_old_in_expr(
                inner,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )
        }
        // Structural recursion for all other variants.
        PureExpr::Var(_, _) | PureExpr::Int(_) | PureExpr::Bool(_) => Ok(expr.clone()),
        PureExpr::BinOp(a, op, b) => Ok(PureExpr::BinOp(
            Arc::new(rewrite_old_in_expr(
                a,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
            *op,
            Arc::new(rewrite_old_in_expr(
                b,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
        )),
        PureExpr::UnOp(op, inner) => Ok(PureExpr::UnOp(
            *op,
            Arc::new(rewrite_old_in_expr(
                inner,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
        )),
        PureExpr::Deref(inner) => Ok(PureExpr::Deref(Arc::new(rewrite_old_in_expr(
            inner,
            arg_names,
            mut_ref_params,
            pre_loop_written_params,
            modified_vars,
        )?))),
        PureExpr::View(inner) => Ok(PureExpr::View(Arc::new(rewrite_old_in_expr(
            inner,
            arg_names,
            mut_ref_params,
            pre_loop_written_params,
            modified_vars,
        )?))),
        PureExpr::Final(inner) => Ok(PureExpr::Final(Arc::new(rewrite_old_in_expr(
            inner,
            arg_names,
            mut_ref_params,
            pre_loop_written_params,
            modified_vars,
        )?))),
        PureExpr::Ite(c, t, e) => Ok(PureExpr::Ite(
            Arc::new(rewrite_old_in_expr(
                c,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
            Arc::new(rewrite_old_in_expr(
                t,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
            Arc::new(rewrite_old_in_expr(
                e,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
        )),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_recv = rewrite_old_in_expr(
                receiver,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?;
            let new_args: Result<Vec<_>, _> = args
                .iter()
                .map(|a| {
                    rewrite_old_in_expr(
                        a,
                        arg_names,
                        mut_ref_params,
                        pre_loop_written_params,
                        modified_vars,
                    )
                })
                .collect();
            Ok(PureExpr::MethodCall {
                receiver: Arc::new(new_recv),
                method: method.clone(),
                args: new_args?,
            })
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args: Result<Vec<_>, _> = args
                .iter()
                .map(|a| {
                    rewrite_old_in_expr(
                        a,
                        arg_names,
                        mut_ref_params,
                        pre_loop_written_params,
                        modified_vars,
                    )
                })
                .collect();
            Ok(PureExpr::LogicFnCall {
                name: name.clone(),
                args: new_args?,
            })
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_body = rewrite_old_in_expr(
                body,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?;
            let new_triggers: Result<Vec<Vec<PureExpr>>, _> = triggers
                .iter()
                .map(|group| {
                    group
                        .iter()
                        .map(|t| {
                            rewrite_old_in_expr(
                                t,
                                arg_names,
                                mut_ref_params,
                                pre_loop_written_params,
                                modified_vars,
                            )
                        })
                        .collect()
                })
                .collect();
            Ok(PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(new_body),
                triggers: new_triggers?,
            })
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_body = rewrite_old_in_expr(
                body,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?;
            let new_triggers: Result<Vec<Vec<PureExpr>>, _> = triggers
                .iter()
                .map(|group| {
                    group
                        .iter()
                        .map(|t| {
                            rewrite_old_in_expr(
                                t,
                                arg_names,
                                mut_ref_params,
                                pre_loop_written_params,
                                modified_vars,
                            )
                        })
                        .collect()
                })
                .collect();
            Ok(PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(new_body),
                triggers: new_triggers?,
            })
        }
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee = rewrite_old_in_expr(
                scrutinee,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?;
            let new_arms: Result<Vec<_>, _> = arms
                .iter()
                .map(|arm| {
                    let new_body = rewrite_old_in_expr(
                        &arm.body,
                        arg_names,
                        mut_ref_params,
                        pre_loop_written_params,
                        modified_vars,
                    )?;
                    Ok(trust_wp_core::formula::MatchArm {
                        pattern: arm.pattern.clone(),
                        body: new_body,
                    })
                })
                .collect();
            Ok(PureExpr::Match {
                scrutinee: Arc::new(new_scrutinee),
                arms: new_arms?,
            })
        }
        PureExpr::Let { var, value, body } => Ok(PureExpr::Let {
            var: var.clone(),
            value: Arc::new(rewrite_old_in_expr(
                value,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
            body: Arc::new(rewrite_old_in_expr(
                body,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
        }),
        PureExpr::LetAssume { assumption, body } => Ok(PureExpr::LetAssume {
            assumption: Arc::new(rewrite_old_in_expr(
                assumption,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
            body: Arc::new(rewrite_old_in_expr(
                body,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
        }),
        PureExpr::LetObligation { obligation, body } => Ok(PureExpr::LetObligation {
            obligation: Arc::new(rewrite_old_in_expr(
                obligation,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
            body: Arc::new(rewrite_old_in_expr(
                body,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
        }),
        PureExpr::Closure { params, body } => Ok(PureExpr::Closure {
            params: params.clone(),
            body: Arc::new(rewrite_old_in_expr(
                body,
                arg_names,
                mut_ref_params,
                pre_loop_written_params,
                modified_vars,
            )?),
        }),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => Ok(expr.clone()),
    }
}
