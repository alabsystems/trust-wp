// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Performance regression tests for `expr_mentions_bound_var` (#1937).
//!
//! These tests exercise the HashSet-based bound-variable lookup and the
//! deep-binder traversal path used by eager instantiation matching.

use ntest::timeout;

use super::*;
use crate::verify::expr_mentions_bound_var;

mod ast_matching;
// ── Performance regression: expr_mentions_bound_var (#1937) ────────

/// Scaling test: expr_mentions_bound_var with many bound variables should
/// complete quickly thanks to HashSet-based lookups (O(1) per Var node).
///
/// Before #1937 fix: O(N * V) due to `&[String]` linear scan at every Var.
/// After fix: O(N) — HashSet provides O(1) membership checks.
///
/// Constructs a wide expression with 200 Var leaves and 200 bound variables.
/// Uses a flat LogicFnCall (depth 2) instead of nested BinOps to avoid
/// hitting MAX_ENCODING_DEPTH (128) with the depth guard. (#1294)
/// With the old O(N * V) algorithm this would be 40,000 comparisons; the
/// HashSet version does 200 lookups.
#[test]
#[timeout(5000)]
fn mentions_bound_var_scales_with_many_bound_vars() {
    // Build a flat LogicFnCall with 200 Var arguments (depth = 2, not 200)
    let args: Vec<PureExpr> = (0..200).map(|i| var(&format!("x{i}"))).collect();
    let expr = logic_fn_call("wide_fn", args);

    // All 200 variables are bound
    let bound: Vec<String> = (0..200).map(|i| format!("x{i}")).collect();
    assert!(expr_mentions_bound_var(&expr, &bound));

    // None of the 200 variables are bound (different names)
    let unbound: Vec<String> = (0..200).map(|i| format!("y{i}")).collect();
    assert!(!expr_mentions_bound_var(&expr, &unbound));
}

/// Scaling test: expr_mentions_bound_var with deep nesting of binders
/// should not allocate O(D) cloned Vecs. (#1937)
///
/// Before fix: each Forall/Let node cloned and filtered the bound_vars Vec.
/// After fix: in-place add/remove on HashSet — zero per-binder allocation.
#[test]
#[timeout(5000)]
fn mentions_bound_var_deep_binders_no_clone_explosion() {
    // Build deeply nested forall: forall a0. forall a1. ... forall a99. x > 0
    let mut expr = gt(var("x"), int(0));
    for i in (0..100).rev() {
        expr = forall(&format!("a{i}"), expr);
    }

    let bound = vec!["x".to_string()];
    // x is mentioned deep inside 100 nested foralls, none of which shadow x
    assert!(expr_mentions_bound_var(&expr, &bound));

    // Now x is shadowed by one of the foralls
    let mut expr_shadowed = gt(var("x"), int(0));
    for i in (0..100).rev() {
        let name = if i == 50 {
            "x".to_string()
        } else {
            format!("a{i}")
        };
        expr_shadowed = forall(&name, expr_shadowed);
    }
    // x is shadowed by forall at depth 50 — the inner x is quantifier-bound
    assert!(!expr_mentions_bound_var(&expr_shadowed, &bound));
}
