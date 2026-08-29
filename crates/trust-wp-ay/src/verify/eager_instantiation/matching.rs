// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern matching and normalization for eager instantiation.
//!
//! Contains expression matching logic (`try_match_expr`), structural equality,
//! bound variable detection, and Deref/Final normalization used by the eager
//! existential instantiation engine.

use trust_wp_core::formula::{PureExpr, PureExprDepthLimitedTraversalExt as _};

use super::{structural_eq::exprs_structurally_equal, MethodCallPattern};
use crate::encoder::{sort_context::DerivedKind, MAX_ENCODING_DEPTH};

/// Normalize a PureExpr by flattening Deref and Final wrappers into variable
/// name suffixes. This bridges the gap between call-site assumption expressions
/// (which use `Deref(Var("f"))` for `(*self)` and `Final(Var("f"))` for `^self`)
/// and ensures body expressions (which use bare `Var("f")` and bound variables).
///
/// Rules:
/// - `Deref(Var("x"))` -> `Var("x")` (by-value dereference identity)
/// - `Final(Var("x"))` -> `Var("x_final")`
/// - `Final(Final(Var("x")))` -> `Var("x_final_final")`
/// - Other expressions are recursively normalized.
pub(crate) fn normalize_deref_final(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up_with_depth_limit(MAX_ENCODING_DEPTH, |node| match node {
        // *x = x for by-value parameters
        PureExpr::Deref(inner) => inner.as_ref().clone(),
        // ^x = x_final
        PureExpr::Final(inner) => match inner.as_ref() {
            PureExpr::Var(name, sort) => {
                PureExpr::Var(DerivedKind::Final.format_name(name), sort.clone())
            }
            _ => PureExpr::Final(inner),
        },
        other => other,
    })
}

/// Check if an expression mentions any of the given variable names as free
/// occurrences.
///
/// Delegates to `PureExpr::any_free_var` for exhaustive binder-aware traversal,
/// preventing silent gaps when new PureExpr variants are added. (#2577)
pub(crate) fn expr_mentions_bound_var(expr: &PureExpr, bound_vars: &[String]) -> bool {
    let set: std::collections::HashSet<&str> = bound_vars.iter().map(String::as_str).collect();
    expr.any_free_var(|name, _sort| set.contains(name))
}

/// Try to match a body postcondition_mut call against a ground call.
/// Returns new variable bindings if the match succeeds.
pub(crate) fn try_match_method_call(
    body_call: &MethodCallPattern<'_>,
    ground_call: &MethodCallPattern<'_>,
    bound_vars: &[String],
    existing_binding: &std::collections::HashMap<String, PureExpr>,
) -> Option<Vec<(String, PureExpr)>> {
    // Both must have the same number of args
    if body_call.args.len() != ground_call.args.len() {
        return None;
    }

    let mut new_bindings = Vec::new();

    // Try to match receiver
    if !try_match_expr(
        body_call.receiver,
        ground_call.receiver,
        bound_vars,
        existing_binding,
        &mut new_bindings,
    ) {
        return None;
    }

    // Try to match each arg
    for (body_arg, ground_arg) in body_call.args.iter().zip(ground_call.args.iter()) {
        if !try_match_expr(
            body_arg,
            ground_arg,
            bound_vars,
            existing_binding,
            &mut new_bindings,
        ) {
            return None;
        }
    }

    Some(new_bindings)
}

/// Try to match a resolve body arg against a ground resolve arg.
pub(crate) fn try_match_resolve_call(
    body_arg: &PureExpr,
    ground_arg: &PureExpr,
    bound_vars: &[String],
    existing_binding: &std::collections::HashMap<String, PureExpr>,
) -> Option<Vec<(String, PureExpr)>> {
    let mut new_bindings = Vec::new();
    if try_match_expr(
        body_arg,
        ground_arg,
        bound_vars,
        existing_binding,
        &mut new_bindings,
    ) {
        Some(new_bindings)
    } else {
        None
    }
}

/// Try to match a body expression against a ground expression.
/// If the body expr is a bound variable, record the binding.
/// If it's a concrete expression, compare structurally (after applying existing bindings).
pub(crate) fn try_match_expr(
    body_expr: &PureExpr,
    ground_expr: &PureExpr,
    bound_vars: &[String],
    existing_binding: &std::collections::HashMap<String, PureExpr>,
    new_bindings: &mut Vec<(String, PureExpr)>,
) -> bool {
    match body_expr {
        PureExpr::Var(name, _) if bound_vars.contains(name) => {
            // This is a bound variable — try to bind it
            if let Some(existing) = existing_binding.get(name) {
                // Already bound — must match
                exprs_structurally_equal(existing, ground_expr)
            } else if let Some((_, existing_val)) = new_bindings.iter().find(|(n, _)| n == name) {
                // Bound in this round — must match
                exprs_structurally_equal(existing_val, ground_expr)
            } else {
                // Fresh binding
                new_bindings.push((name.clone(), ground_expr.clone()));
                true
            }
        }
        PureExpr::Var(name, _sort) => {
            // Free variable — check if already bound to a value, else compare by name
            if let Some(bound_val) = existing_binding.get(name) {
                exprs_structurally_equal(bound_val, ground_expr)
            } else {
                // Must match exactly (same variable name)
                matches!(ground_expr, PureExpr::Var(gn, _) if gn == name)
            }
        }
        PureExpr::LogicFnCall { name, args } => {
            if let PureExpr::LogicFnCall { name: gn, args: ga } = ground_expr {
                if name != gn || args.len() != ga.len() {
                    return false;
                }
                for (a, g) in args.iter().zip(ga.iter()) {
                    if !try_match_expr(a, g, bound_vars, existing_binding, new_bindings) {
                        return false;
                    }
                }
                true
            } else {
                false
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if let PureExpr::MethodCall {
                receiver: gr,
                method: gm,
                args: ga,
            } = ground_expr
            {
                if method != gm || args.len() != ga.len() {
                    return false;
                }
                if !try_match_expr(receiver, gr, bound_vars, existing_binding, new_bindings) {
                    return false;
                }
                for (a, g) in args.iter().zip(ga.iter()) {
                    if !try_match_expr(a, g, bound_vars, existing_binding, new_bindings) {
                        return false;
                    }
                }
                true
            } else {
                false
            }
        }
        _ => exprs_structurally_equal(body_expr, ground_expr),
    }
}
