// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure-capture substitution for ensures expressions.

use std::sync::Arc;

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_arity},
    MatchArm, PureExpr,
};

use super::super::helpers::expr_references_var_name;
use crate::callbacks::final_receiver_state_expr;

/// Substitute closure capture variable names in a postcondition expression
/// with their tuple field projections, handling `Old()` context correctly.
///
/// When a concrete closure's ensures clause references capture variables by name
/// (e.g., `x@ == old(x@+1)`), the bare `Var("x")` must be replaced with the
/// appropriate tuple field projection from the closure environment:
/// - Outside `Old()`: `x` -> `tuple_get_N(Final(self_expr))` (post-call state)
/// - Inside `Old()`: `x` -> `tuple_get_N(self_expr)` (pre-call state), `Old` stripped
///
/// This is needed because `apply_postconditions_with_self` treats capture names
/// as regular free variables (they're not in the symbolic names list), so they
/// pass through unsubstituted. (#970)
pub(in crate::mir_analysis::extract) fn substitute_capture_fields_in_postcondition(
    expr: &PureExpr,
    capture_bindings: &[(usize, String)],
    self_expr: &PureExpr,
    inside_old: bool,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, _sort) => {
            for (field_idx, capture_name) in capture_bindings {
                if name == capture_name {
                    let state_expr = if inside_old {
                        // Pre-call state: project from current self_expr.
                        self_expr.clone()
                    } else {
                        // Post-call state: project from Final(self_expr).
                        final_receiver_state_expr(self_expr)
                    };
                    let projection = project_capture_field(&state_expr, *field_idx);
                    return projection;
                }
            }
            expr.clone()
        }
        PureExpr::Old(inner) => {
            // Recurse into Old with inside_old=true, then strip the Old wrapper
            // since the capture projection already targets the pre-state.
            let transformed = substitute_capture_fields_in_postcondition(
                inner,
                capture_bindings,
                self_expr,
                true,
            );
            // Only preserve Old when no capture variable is referenced.
            //
            // With tuple-projection simplification, a capture substitution can
            // become syntactically identical (`Old(x)` -> `x` inside Old). We
            // must still strip `Old` in that case because the pre-state was
            // already selected by `inside_old=true`.
            let references_capture = capture_bindings
                .iter()
                .any(|(_, capture_name)| expr_references_var_name(inner, capture_name));
            if &transformed == inner.as_ref() && !references_capture {
                PureExpr::Old(Arc::new(transformed))
            } else {
                transformed
            }
        }
        PureExpr::Bool(_) | PureExpr::Int(_) => expr.clone(),
        PureExpr::BinOp(l, op, r) => PureExpr::BinOp(
            Arc::new(substitute_capture_fields_in_postcondition(
                l,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            *op,
            Arc::new(substitute_capture_fields_in_postcondition(
                r,
                capture_bindings,
                self_expr,
                inside_old,
            )),
        ),
        PureExpr::UnOp(op, operand) => PureExpr::UnOp(
            *op,
            Arc::new(substitute_capture_fields_in_postcondition(
                operand,
                capture_bindings,
                self_expr,
                inside_old,
            )),
        ),
        PureExpr::Ite(c, t, e) => PureExpr::Ite(
            Arc::new(substitute_capture_fields_in_postcondition(
                c,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            Arc::new(substitute_capture_fields_in_postcondition(
                t,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            Arc::new(substitute_capture_fields_in_postcondition(
                e,
                capture_bindings,
                self_expr,
                inside_old,
            )),
        ),
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(substitute_capture_fields_in_postcondition(
                inner,
                capture_bindings,
                self_expr,
                inside_old,
            )))
        }
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(substitute_capture_fields_in_postcondition(
                inner,
                capture_bindings,
                self_expr,
                inside_old,
            )))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(substitute_capture_fields_in_postcondition(
                inner,
                capture_bindings,
                self_expr,
                inside_old,
            )))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(substitute_capture_fields_in_postcondition(
                receiver,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|a| {
                    substitute_capture_fields_in_postcondition(
                        a,
                        capture_bindings,
                        self_expr,
                        inside_old,
                    )
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|a| {
                    substitute_capture_fields_in_postcondition(
                        a,
                        capture_bindings,
                        self_expr,
                        inside_old,
                    )
                })
                .collect(),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(substitute_capture_fields_in_postcondition(
                assumption,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            body: Arc::new(substitute_capture_fields_in_postcondition(
                body,
                capture_bindings,
                self_expr,
                inside_old,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(substitute_capture_fields_in_postcondition(
                obligation,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            body: Arc::new(substitute_capture_fields_in_postcondition(
                body,
                capture_bindings,
                self_expr,
                inside_old,
            )),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(substitute_capture_fields_in_postcondition(
                value,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            body: Arc::new(substitute_capture_fields_in_postcondition(
                body,
                capture_bindings,
                self_expr,
                inside_old,
            )),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(substitute_capture_fields_in_postcondition(
                body,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            triggers: triggers
                .iter()
                .map(|t| {
                    t.iter()
                        .map(|e| {
                            substitute_capture_fields_in_postcondition(
                                e,
                                capture_bindings,
                                self_expr,
                                inside_old,
                            )
                        })
                        .collect()
                })
                .collect(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(substitute_capture_fields_in_postcondition(
                body,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            triggers: triggers
                .iter()
                .map(|t| {
                    t.iter()
                        .map(|e| {
                            substitute_capture_fields_in_postcondition(
                                e,
                                capture_bindings,
                                self_expr,
                                inside_old,
                            )
                        })
                        .collect()
                })
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(substitute_capture_fields_in_postcondition(
                scrutinee,
                capture_bindings,
                self_expr,
                inside_old,
            )),
            arms: arms
                .iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern.clone(),
                    body: substitute_capture_fields_in_postcondition(
                        &arm.body,
                        capture_bindings,
                        self_expr,
                        inside_old,
                    ),
                })
                .collect(),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params: params.clone(),
            body: Arc::new(substitute_capture_fields_in_postcondition(
                body,
                capture_bindings,
                self_expr,
                inside_old,
            )),
        },
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}

pub(in crate::mir_analysis::extract) fn project_capture_field(
    state_expr: &PureExpr,
    field_idx: usize,
) -> PureExpr {
    if let PureExpr::LogicFnCall { name, args } = state_expr {
        if tuple_logic_fn_arity(name) == Some(args.len()) {
            if let Some(arg) = args.get(field_idx) {
                return normalize_tracked_capture_projection(arg.clone());
            }
        }
    }
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(field_idx),
        args: vec![state_expr.clone()],
    }
}

fn normalize_tracked_capture_projection(expr: PureExpr) -> PureExpr {
    match expr {
        PureExpr::Var(name, sort) if name.starts_with("self.") => {
            PureExpr::Deref(Arc::new(PureExpr::Var(name, sort)))
        }
        PureExpr::Final(inner) => match inner.as_ref() {
            PureExpr::Var(name, sort) if name.starts_with("self.") => PureExpr::Final(Arc::new(
                PureExpr::Deref(Arc::new(PureExpr::Var(name.clone(), sort.clone()))),
            )),
            _ => PureExpr::Final(inner),
        },
        other => other,
    }
}
