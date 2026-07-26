// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutable-reference postcondition transforms.
//!
//! Implements the RustHorn-style encoding transform:
//! - `Deref(Var(x))` → `Final(Var(x))` outside `old(...)` for mut-ref params
//! - `Old(Deref(Var(x)))` stays unchanged (already references initial value)
//! - Bare `Var(x)` for mut-ref params → `Deref(Var(x))` (normalizes to `x_current`)
//!
//! Also includes the pre-scan that detects explicit `Final(Var(x))` usage,
//! which suppresses the automatic `Deref` → `Final` transform for that param.

use std::{collections::HashSet, sync::Arc};

use super::{
    super::pure_expr::{ExprSort, PureExpr},
    traversal::{rewrite_with_old_context, visit_with_old_context},
};

/// Rewrite a postcondition for mutable-borrow verification.
///
/// See [`PureExpr::transform_postcondition_for_mut_refs`] for full docs.
pub(crate) fn transform_postcondition_for_mut_refs(
    expr: &PureExpr,
    mut_ref_params: &HashSet<String>,
) -> PureExpr {
    let explicit_final_vars = collect_explicit_final_mut_refs(expr, mut_ref_params);
    rewrite_with_old_context(expr, false, &mut |node, inside_old| {
        rewrite_mut_ref_node(node, inside_old, mut_ref_params, &explicit_final_vars)
    })
}

/// Pre-scan: collect mut-ref params that already have explicit `Final(Var(name))`
/// outside `old(...)`. When the user writes `^x` explicitly, we preserve `*x`
/// as current-state reads instead of rewriting them to `^x` again.
fn collect_explicit_final_mut_refs(
    expr: &PureExpr,
    mut_ref_params: &HashSet<String>,
) -> HashSet<String> {
    let mut explicit = HashSet::new();
    visit_with_old_context(expr, false, &mut |node, inside_old| {
        if !inside_old {
            if let PureExpr::Final(inner) = node {
                if let PureExpr::Var(name, _) = inner.as_ref() {
                    if mut_ref_params.contains(name) {
                        explicit.insert(name.clone());
                    }
                }
            }
        }
    });
    explicit
}

/// Node-local rewrite rule for mut-ref postconditions.
///
/// Returns `Some(expr)` when the node should be replaced, `None` to continue
/// with generic recursion.
fn rewrite_mut_ref_node(
    node: &PureExpr,
    inside_old: bool,
    mut_ref_params: &HashSet<String>,
    explicit_final_vars: &HashSet<String>,
) -> Option<PureExpr> {
    match node {
        // `DerefMut::deref_mut` trait specs quantify over the whole `&mut T`
        // receiver.  Do not normalize the first postcondition/precondition
        // argument from `x` to `*x`, or the user clause stops matching the
        // call-site assumption emitted from the std spec.
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if matches!(method.as_str(), "precondition" | "postcondition")
            && is_deref_mut_receiver(receiver.as_ref()) =>
        {
            Some(PureExpr::MethodCall {
                receiver: receiver.clone(),
                method: method.clone(),
                args: args.clone(),
            })
        }
        // Bare Var("x") for &mut params → Deref(Var("x")) to map to `x_current`
        // in SMT, not an unconstrained variable. (#609)
        PureExpr::Var(name, sort) => {
            if matches!(sort, Some(ExprSort::MutRef(_))) {
                return None; // whole-borrow MutRef sort — don't rewrite
            }
            if mut_ref_params.contains(name) {
                Some(PureExpr::Deref(Arc::new(PureExpr::Var(
                    name.clone(),
                    sort.clone(),
                ))))
            } else {
                None
            }
        }
        // Key transform: Deref(Var(x)) → Final(Var(x)) for mut-ref params,
        // but only outside Old() and when the user hasn't written explicit ^x.
        PureExpr::Deref(inner) => {
            if let PureExpr::Var(name, sort) = inner.as_ref() {
                if mut_ref_params.contains(name) {
                    let v = PureExpr::Var(name.clone(), sort.clone());
                    return Some(if !inside_old && !explicit_final_vars.contains(name) {
                        PureExpr::Final(Arc::new(v))
                    } else {
                        PureExpr::Deref(Arc::new(v))
                    });
                }
            }
            None // not a mut-ref param — let generic recursion handle it
        }
        // Already Final — if inner is a mut-ref Var, don't recurse to avoid
        // double-wrapping Var → Deref(Var). (#609)
        PureExpr::Final(inner) => {
            if let PureExpr::Var(name, sort) = inner.as_ref() {
                if mut_ref_params.contains(name) {
                    let v = PureExpr::Var(name.clone(), sort.clone());
                    return Some(PureExpr::Final(Arc::new(v)));
                }
            }
            None
        }
        _ => None,
    }
}

fn is_deref_mut_receiver(receiver: &PureExpr) -> bool {
    matches!(receiver, PureExpr::Var(name, _) if name.ends_with("deref_mut") || name.contains("::deref_mut"))
}
