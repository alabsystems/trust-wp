// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bool-result inference from postconditions.

use ay_dpll::api::Sort;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};

use crate::encoder::AYEncoder;

/// Fallback bool-sort detector for `result` from postconditions.
///
/// This covers alias-return cases where `return_expr` is a temporary variable
/// (e.g., `_call_0`) and we must still force `result` to Bool for
/// `result == true` style postconditions.
#[cfg(test)]
pub(crate) fn result_is_bool_by_postcondition(ensures: &[PureExpr]) -> bool {
    ensures.iter().any(|expr| {
        let mut counterpart_is_bool =
            |counterpart: &PureExpr| expr_definitely_bool_for_result_inference(counterpart);
        expr_requires_result_bool_impl(expr, &mut counterpart_is_bool)
    })
}

/// Context-aware Bool detector for `result` from postconditions.
///
/// Unlike [`result_is_bool_by_postcondition`], this helper can consult encoder
/// declarations and sort hints for counterpart expressions such as
/// `result == my_pred(x)`.
pub(crate) fn result_is_bool_by_postcondition_with_context(
    encoder: &mut AYEncoder,
    ensures: &[PureExpr],
) -> bool {
    ensures.iter().any(|expr| {
        let mut counterpart_is_bool = |counterpart: &PureExpr| {
            encoder.infer_expr_sort_with_context(counterpart, None) == Sort::Bool
                || expr_definitely_bool_for_result_inference(counterpart)
        };
        expr_requires_result_bool_impl(expr, &mut counterpart_is_bool)
    })
}

/// Check whether a single expression requires `result` to have Bool sort.
///
/// `And`/`Or`/`Implies` are logical connectors - their operands are Bool
/// sub-expressions, but variables nested inside comparisons (e.g., `result > x`)
/// remain Int. So we recurse through connectors rather than treating them as
/// evidence that `result` is Bool.
#[cfg(test)]
pub(crate) fn expr_requires_result_bool(expr: &PureExpr) -> bool {
    let mut counterpart_is_bool =
        |counterpart: &PureExpr| expr_definitely_bool_for_result_inference(counterpart);
    expr_requires_result_bool_impl(expr, &mut counterpart_is_bool)
}

fn is_direct_result_var(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == "result")
}

fn method_returns_bool_for_result_inference(method: &str) -> bool {
    matches!(
        method,
        "precondition"
            | "postcondition"
            | "postcondition_once"
            | "postcondition_mut"
            | "is_some"
            | "is_none"
            | "is_ok"
            | "is_err"
            | "contains"
            | "completed"
            | "produces"
            | "ext_eq"
            | "is_empty"
    ) || trust_wp_core::logic::is_invariant_method_name(method)
}

fn logic_fn_returns_bool_for_result_inference(name: &str) -> bool {
    matches!(name, "resolve" | "fmap_contains")
        || name == "inv"
        || name.ends_with("_inv")
        || trust_wp_core::logic::is_invariant_method_name(name)
}

fn expr_definitely_bool_for_result_inference(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Bool(_) => true,
        PureExpr::Var(_, Some(ExprSort::Bool)) => true,
        PureExpr::BinOp(_, op, _) => matches!(
            op,
            BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or
                | BinOp::Implies
        ),
        PureExpr::UnOp(UnOp::Not, _) => true,
        PureExpr::Ite(_, then_expr, else_expr) => {
            expr_definitely_bool_for_result_inference(then_expr)
                && expr_definitely_bool_for_result_inference(else_expr)
        }
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => true,
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_definitely_bool_for_result_inference(inner),
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => expr_definitely_bool_for_result_inference(body),
        PureExpr::MethodCall { method, .. } => method_returns_bool_for_result_inference(method),
        PureExpr::LogicFnCall { name, .. } => logic_fn_returns_bool_for_result_inference(name),
        PureExpr::Match { arms, .. } => {
            !arms.is_empty()
                && arms
                    .iter()
                    .all(|arm| expr_definitely_bool_for_result_inference(&arm.body))
        }
        _ => false,
    }
}

fn expr_requires_result_bool_impl(
    expr: &PureExpr,
    counterpart_is_bool: &mut impl FnMut(&PureExpr) -> bool,
) -> bool {
    match expr {
        // Bare `result` used as a Bool postcondition.
        PureExpr::Var(name, _) => name == "result",
        // `!expr`: expr is in a Bool context. Recurse to check whether
        // `result` is directly used as Bool (e.g., `!result`) vs inside
        // a comparison (e.g., `!(result > 0)` where result is Int).
        PureExpr::UnOp(UnOp::Not, inner) => {
            expr_requires_result_bool_impl(inner, counterpart_is_bool)
        }
        PureExpr::BinOp(left, op, right) => match op {
            // Logical connectors: recurse - don't treat presence of `result`
            // inside comparisons as evidence of Bool sort.
            BinOp::And | BinOp::Or | BinOp::Implies => {
                expr_requires_result_bool_impl(left, counterpart_is_bool)
                    || expr_requires_result_bool_impl(right, counterpart_is_bool)
            }
            // `result == true` or `result != false` etc.
            BinOp::Eq | BinOp::Ne => {
                // Only a direct `result` operand constrains the result sort.
                // Nested receivers like `__trust_wp_field_flag(result) == true`
                // constrain the call's return sort, not `result` itself. (#2608)
                (is_direct_result_var(left) && counterpart_is_bool(right))
                    || (is_direct_result_var(right) && counterpart_is_bool(left))
            }
            _ => false,
        },
        // `if cond then ... else ...`: the condition is a Bool context.
        // Recurse into condition to check if `result` is directly Bool
        // (e.g., `if result then ...`) vs inside a comparison
        // (e.g., `if result > 0 then ...` where result is Int).
        PureExpr::Ite(cond, _, _) => expr_requires_result_bool_impl(cond, counterpart_is_bool),
        // Quantifier bodies and these wrappers preserve the Bool carrier of
        // their body for result-inference purposes. (#2624)
        PureExpr::Forall { body, .. }
        | PureExpr::Exists { body, .. }
        | PureExpr::Old(body)
        | PureExpr::Deref(body)
        | PureExpr::Final(body)
        | PureExpr::View(body)
        | PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => {
            expr_requires_result_bool_impl(body, counterpart_is_bool)
        }
        _ => false,
    }
}
