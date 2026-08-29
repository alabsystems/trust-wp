// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{ExprSort, PureExpr, PureExprChildRole};

use super::ParsedContract;

/// Simplify newtype field-0 access patterns in a pure expression.
///
/// For params in `newtype_params`:
/// - `LogicFnCall("__trust_wp_tuple_get_0", [X])` -> `X` when X is/contains a newtype param
/// - `Var("param.0")` -> `Var("param")` for closure-capture artifacts
///
/// **Final guard (#2124):** When `tuple_get_0`'s argument contains a `Final`
/// wrapper (e.g., `tuple_get_0(Final(x))`), simplification is suppressed because
/// MIR analysis wraps newtype final values in `tuple1(field_val)`, so
/// `tuple_get_0(x_final)` is needed to decompose the wrapped value.
pub(in crate::callbacks) fn simplify_newtype_field_access_expr(
    expr: &PureExpr,
    newtype_params: &HashSet<String>,
) -> PureExpr {
    simplify_newtype_field_access_inner(expr, newtype_params, false)
}

/// Inner recursive helper with `inside_final` context flag.
///
/// When `inside_final` is true, we are recursing inside a `Final(...)` wrapper.
/// In that position, `tuple_get_0(x)` generally must NOT be simplified to `x`
/// because the MIR analysis wraps newtype final values in `tuple1(field_val)`,
/// and the postcondition needs `tuple_get_0(x_final) == val` to decompose it
/// via the tuple axiom `tuple_get_0(tuple1(v)) = v`. Simplifying away the
/// `tuple_get_0` produces `x_final == val` where `x_final` is a tuple — sort
/// mismatch or unconstrained (#2124).
///
/// User-written postconditions like `^x.0` parse as
/// `Final(tuple_get_0(Var("x")))`. That field projection must be preserved so
/// the encoder can decompose the tuple1-wrapped final value extracted from MIR.
fn simplify_newtype_field_access_inner(
    expr: &PureExpr,
    newtype_params: &HashSet<String>,
    inside_final: bool,
) -> PureExpr {
    use trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX;

    expr.rewrite_bottom_up_with_context(
        inside_final,
        |inside_final, role, _| *inside_final || role == PureExprChildRole::FinalInner,
        |node, node_inside_final| match node {
            PureExpr::Var(name, sort) => {
                // Handle closure capture artifact: "self.0" -> "self"
                if let Some(base) = name.strip_suffix(".0") {
                    if newtype_params.contains(base) && !*node_inside_final {
                        return PureExpr::Var(base.to_string(), sort);
                    }
                }
                PureExpr::Var(name, sort)
            }
            PureExpr::LogicFnCall { name, args } => {
                // Simplify tuple_get_0(X) -> X when X is a newtype param.
                //
                // Guard (#2124): when the arg itself contains a `Final` wrapper
                // (e.g., `tuple_get_0(Final(x))`), the simplification is blocked
                // because MIR-derived final values are tuple1-wrapped and need
                // the accessor to decompose them.
                //
                if name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX)
                    && args.len() == 1
                    && name
                        .strip_prefix(TUPLE_FIELD_LOGIC_FN_PREFIX)
                        .is_some_and(|idx_str| idx_str == "0")
                {
                    let simplified_arg = args[0].clone();
                    if *node_inside_final {
                        if let PureExpr::Var(param_name, _) = &simplified_arg {
                            if newtype_params.contains(param_name.as_str()) {
                                return PureExpr::Var(format!("{param_name}.0"), None);
                            }
                            if param_name
                                .strip_suffix(".0")
                                .is_some_and(|base| newtype_params.contains(base))
                            {
                                return PureExpr::Var(param_name.clone(), None);
                            }
                        }
                    }
                    match ref_like_newtype_param_projection(&simplified_arg, newtype_params) {
                        RefLikeProjection::BareParam => {
                            return PureExpr::LogicFnCall {
                                name,
                                args: vec![PureExpr::Deref(Arc::new(simplified_arg))],
                            };
                        }
                        RefLikeProjection::ProjectedParam => {
                            return PureExpr::LogicFnCall {
                                name,
                                args: vec![simplified_arg],
                            };
                        }
                        RefLikeProjection::No => {}
                    }
                    if is_newtype_param_expr(&simplified_arg, newtype_params)
                        && !*node_inside_final
                        && !expr_contains_final(&simplified_arg)
                    {
                        return simplified_arg;
                    }
                }

                PureExpr::LogicFnCall { name, args }
            }
            other => other,
        },
    )
}

/// Check whether an expression refers to a newtype parameter variable.
///
/// Looks through `Deref`, `Old`, `Final`, and `View` wrappers to find
/// the underlying `Var` name.
pub(super) fn is_newtype_param_expr(expr: &PureExpr, newtype_params: &HashSet<String>) -> bool {
    match expr {
        PureExpr::Var(name, _) => newtype_params.contains(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => is_newtype_param_expr(inner, newtype_params),
        _ => false,
    }
}

enum RefLikeProjection {
    No,
    BareParam,
    ProjectedParam,
}

fn ref_like_newtype_param_projection(
    expr: &PureExpr,
    newtype_params: &HashSet<String>,
) -> RefLikeProjection {
    match expr {
        PureExpr::Var(name, Some(ExprSort::Ref(_) | ExprSort::MutRef(_)))
            if newtype_params.contains(name.as_str()) =>
        {
            RefLikeProjection::BareParam
        }
        PureExpr::Deref(inner)
            if matches!(
                inner.as_ref(),
                PureExpr::Var(name, Some(ExprSort::Ref(_) | ExprSort::MutRef(_)))
                    if newtype_params.contains(name.as_str())
            ) =>
        {
            RefLikeProjection::ProjectedParam
        }
        _ => RefLikeProjection::No,
    }
}

/// Check whether an expression contains a `Final` wrapper anywhere on the
/// path to the underlying variable.
///
/// Used to guard the `tuple_get_0` simplification: when the argument is
/// inside a `Final`, the simplification must not apply because MIR analysis
/// wraps newtype final values in `tuple1(field_val)`, and the postcondition
/// needs `tuple_get_0(x_final)` to decompose it (#2124).
fn expr_contains_final(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Final(_) => true,
        PureExpr::Deref(inner) | PureExpr::Old(inner) | PureExpr::View(inner) => {
            expr_contains_final(inner)
        }
        _ => false,
    }
}

/// Apply newtype field-0 simplification to all expressions in a parsed contract.
pub(super) fn simplify_newtype_field_access_in_contract(
    parsed: &mut ParsedContract,
    newtype_params: &HashSet<String>,
) {
    if newtype_params.is_empty() {
        return;
    }
    parsed.rewrite_all_exprs(|expr| simplify_newtype_field_access_expr(expr, newtype_params));
}
