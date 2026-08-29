// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Capture variable substitution with concrete tuple field projections.

use std::sync::Arc;

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_arity},
    PureExpr,
};

use crate::callbacks::proof_assert_extract::collapse_idempotent_views;

/// Project a capture field out of a state expression, simplifying the
/// constructor-projection identity `tuple_get_i(tupleN(f_0, ..)) → f_i` when
/// the state is a literal tuple constructor. (#closure-capture-carriers)
///
/// The simplification is exact and mirrors `project_capture_field` in the
/// extraction pipeline. It matters for carrier-bearing environments: the field
/// of `tuple1(Final(<MutRef carrier>))` must reach the encoder as the direct
/// `Final(<carrier>)` projection — routing it through the `tuple_get_0` getter
/// UF instead forces a cross-sort tuple family whose paired axiom degrades to
/// a sort-coerced (useless) quantifier.
fn project_state_field(state: &PureExpr, field_idx: usize) -> PureExpr {
    if let PureExpr::LogicFnCall { name, args } = state {
        if tuple_logic_fn_arity(name) == Some(args.len()) {
            if let Some(arg) = args.get(field_idx) {
                return arg.clone();
            }
        }
    }
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(field_idx),
        args: vec![state.clone()],
    }
}

/// Substitute capture variables with tuple field projections on concrete
/// pre/post state expressions using concrete `PureExpr` values rather than
/// axiom-side placeholder variable names.
pub(in crate::callbacks) fn substitute_captures_inline(
    expr: &PureExpr,
    capture_bindings: &[(usize, String)],
    pre_state: &PureExpr,
    post_state: &PureExpr,
    result_expr: &PureExpr,
    inside_old: bool,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, _sort) => {
            if name == "result" {
                return collapse_idempotent_views(result_expr.clone());
            }
            for (field_idx, capture_name) in capture_bindings {
                if name == capture_name {
                    let state = if inside_old { pre_state } else { post_state };
                    return project_state_field(state, *field_idx);
                }
            }
            expr.clone()
        }
        PureExpr::Old(inner) => {
            let transformed = substitute_captures_inline(
                inner,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                true,
            );
            if &transformed == inner.as_ref() {
                PureExpr::Old(Arc::new(transformed))
            } else {
                transformed
            }
        }
        PureExpr::Bool(_) | PureExpr::Int(_) => expr.clone(),
        PureExpr::BinOp(l, op, r) => PureExpr::BinOp(
            Arc::new(substitute_captures_inline(
                l,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            *op,
            Arc::new(substitute_captures_inline(
                r,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
        ),
        PureExpr::UnOp(op, operand) => PureExpr::UnOp(
            *op,
            Arc::new(substitute_captures_inline(
                operand,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
        ),
        PureExpr::Ite(c, t, e) => PureExpr::Ite(
            Arc::new(substitute_captures_inline(
                c,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            Arc::new(substitute_captures_inline(
                t,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            Arc::new(substitute_captures_inline(
                e,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
        ),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(substitute_captures_inline(
            inner,
            capture_bindings,
            pre_state,
            post_state,
            result_expr,
            inside_old,
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(substitute_captures_inline(
            inner,
            capture_bindings,
            pre_state,
            post_state,
            result_expr,
            inside_old,
        ))),
        PureExpr::View(inner) => {
            collapse_idempotent_views(PureExpr::View(Arc::new(substitute_captures_inline(
                inner,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            ))))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(substitute_captures_inline(
                receiver,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|a| {
                    substitute_captures_inline(
                        a,
                        capture_bindings,
                        pre_state,
                        post_state,
                        result_expr,
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
                    substitute_captures_inline(
                        a,
                        capture_bindings,
                        pre_state,
                        post_state,
                        result_expr,
                        inside_old,
                    )
                })
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(substitute_captures_inline(
                body,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            triggers: triggers
                .iter()
                .map(|trig| {
                    trig.iter()
                        .map(|t| {
                            substitute_captures_inline(
                                t,
                                capture_bindings,
                                pre_state,
                                post_state,
                                result_expr,
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
            body: Arc::new(substitute_captures_inline(
                body,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            triggers: triggers
                .iter()
                .map(|trig| {
                    trig.iter()
                        .map(|t| {
                            substitute_captures_inline(
                                t,
                                capture_bindings,
                                pre_state,
                                post_state,
                                result_expr,
                                inside_old,
                            )
                        })
                        .collect()
                })
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(substitute_captures_inline(
                scrutinee,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: substitute_captures_inline(
                        &arm.body,
                        capture_bindings,
                        pre_state,
                        post_state,
                        result_expr,
                        inside_old,
                    ),
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(substitute_captures_inline(
                value,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            body: Arc::new(substitute_captures_inline(
                body,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(substitute_captures_inline(
                assumption,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            body: Arc::new(substitute_captures_inline(
                body,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(substitute_captures_inline(
                obligation,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
            body: Arc::new(substitute_captures_inline(
                body,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params: params.clone(),
            body: Arc::new(substitute_captures_inline(
                body,
                capture_bindings,
                pre_state,
                post_state,
                result_expr,
                inside_old,
            )),
        },
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}
