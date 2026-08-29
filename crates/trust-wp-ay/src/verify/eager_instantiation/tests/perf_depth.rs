// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Guard against O(V × N) from `bound_vars.contains()` on `&[String]`.
///
/// With 200 bound variables and a 200-deep expression tree, `try_match_expr`
/// performs ~40,000 linear scans. This test establishes a timing baseline
/// so that the fix (converting to HashSet) can be validated.
#[test]
#[timeout(30000)]
fn perf_try_match_expr_many_bound_vars() {
    let n_vars = 200;
    let bound_vars: Vec<String> = (0..n_vars).map(|i| format!("v_{i}")).collect();

    // Build a deeply-nested LogicFnCall chain: f(f(f(...f(v_0)...)))
    let mut body_expr = var("v_0");
    let mut ground_expr = var("ground_0");
    for i in 1..n_vars {
        body_expr = logic_fn_call(&format!("f_{i}"), vec![body_expr]);
        ground_expr = logic_fn_call(&format!("f_{i}"), vec![ground_expr]);
    }

    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    // The innermost var("v_0") is a bound variable, so the match should
    // succeed by binding v_0 → ground_0.
    let matched = try_match_expr(
        &body_expr,
        &ground_expr,
        &bound_vars,
        &existing,
        &mut new_bindings,
    );
    assert!(matched, "deep nested match should succeed");
    assert_eq!(new_bindings.len(), 1, "should bind exactly v_0");
    assert_eq!(new_bindings[0].0, "v_0");
}

// ── Depth-boundary regression guards (#2577) ──────────────────────────
//
// `exprs_structurally_equal` and `try_match_expr` are recursive without
// depth limits. Their callers bound input depth via `walk_expr_with_active_binders`
// (MAX_ENCODING_DEPTH = 128), but the functions themselves must not overflow
// the stack at that depth. These tests verify completion at the boundary.

/// Build a left-recursive LogicFnCall chain of depth `n`: f_n(f_{n-1}(...f_1(leaf)...)).
fn build_deep_logic_fn_chain(n: usize, leaf: PureExpr) -> PureExpr {
    let mut expr = leaf;
    for i in 1..=n {
        expr = logic_fn_call(&format!("f_{i}"), vec![expr]);
    }
    expr
}

/// `exprs_structurally_equal` must complete without stack overflow on
/// identical trees at MAX_ENCODING_DEPTH (128).
///
/// The function has no internal depth limit — it relies on callers bounding
/// input depth. This test proves it survives the production depth boundary.
#[test]
#[timeout(5000)]
fn structural_eq_completes_at_max_encoding_depth() {
    let depth = crate::encoder::MAX_ENCODING_DEPTH;

    let a = build_deep_logic_fn_chain(depth, var("leaf"));
    let b = build_deep_logic_fn_chain(depth, var("leaf"));

    assert!(
        exprs_structurally_equal(&a, &b),
        "identical trees at depth {depth} must be structurally equal"
    );
}

/// `exprs_structurally_equal` correctly detects a mismatch in the deepest
/// leaf of a MAX_ENCODING_DEPTH tree. Proves the recursion reaches the
/// bottom without short-circuiting.
#[test]
#[timeout(5000)]
fn structural_eq_detects_deep_leaf_mismatch() {
    let depth = crate::encoder::MAX_ENCODING_DEPTH;

    let a = build_deep_logic_fn_chain(depth, var("leaf_a"));
    let b = build_deep_logic_fn_chain(depth, var("leaf_b"));

    assert!(
        !exprs_structurally_equal(&a, &b),
        "trees with different leaves at depth {depth} must not be equal"
    );
}

/// `try_match_expr` must complete on trees at MAX_ENCODING_DEPTH and
/// successfully bind a bound variable at the deepest leaf.
#[test]
#[timeout(5000)]
fn try_match_expr_completes_at_max_encoding_depth() {
    let depth = crate::encoder::MAX_ENCODING_DEPTH;
    let bound_vars = vec!["bv".to_string()];
    let existing = HashMap::new();
    let mut new_bindings = Vec::new();

    let body = build_deep_logic_fn_chain(depth, var("bv"));
    let ground = build_deep_logic_fn_chain(depth, var("concrete_val"));

    let matched = try_match_expr(&body, &ground, &bound_vars, &existing, &mut new_bindings);
    assert!(matched, "matching at depth {depth} should succeed");
    assert_eq!(new_bindings.len(), 1);
    assert_eq!(new_bindings[0].0, "bv");
    assert!(
        exprs_structurally_equal(&new_bindings[0].1, &var("concrete_val")),
        "bound variable should map to the ground leaf"
    );
}

/// `collect_body_postcondition_mut_calls` respects MAX_ENCODING_DEPTH:
/// a postcondition_mut call nested deeper than the depth limit must not
/// be collected.
#[test]
#[timeout(5000)]
fn collector_skips_postcondition_mut_beyond_depth_limit() {
    let depth = crate::encoder::MAX_ENCODING_DEPTH + 5;

    // Build: f_depth(f_{depth-1}(...postcondition_mut(self, arg)...))
    let deep_call = method_call(var("self"), "postcondition_mut", vec![var("arg")]);
    let expr = build_deep_logic_fn_chain(depth, deep_call);

    let bound_vars = vec!["arg".to_string()];
    let calls = collect_body_postcondition_mut_calls(&expr, &bound_vars);

    assert!(
        calls.is_empty(),
        "postcondition_mut at depth {} (beyond limit {}) should not be collected, \
         but found {} calls",
        depth + 1, // +1 for the method call itself
        crate::encoder::MAX_ENCODING_DEPTH,
        calls.len(),
    );
}

/// `collect_body_postcondition_mut_calls` collects a call at exactly
/// MAX_ENCODING_DEPTH (the last depth that is visited).
#[test]
#[timeout(5000)]
fn collector_finds_postcondition_mut_at_exact_depth_limit() {
    // The walker visits depth 0..=MAX_ENCODING_DEPTH, so a call at depth
    // MAX_ENCODING_DEPTH should still be found.
    let wrapper_depth = crate::encoder::MAX_ENCODING_DEPTH;

    let deep_call = method_call(var("self"), "postcondition_mut", vec![var("arg")]);
    let expr = build_deep_logic_fn_chain(wrapper_depth, deep_call);

    let bound_vars = vec!["arg".to_string()];
    let calls = collect_body_postcondition_mut_calls(&expr, &bound_vars);

    // At exactly MAX_ENCODING_DEPTH wrappers, the MethodCall node sits at
    // depth = wrapper_depth. The walker's guard is `if depth > MAX_ENCODING_DEPTH`
    // (strict), so depth == MAX_ENCODING_DEPTH is still visited.
    assert_eq!(
        calls.len(),
        1,
        "postcondition_mut at exact depth limit ({wrapper_depth}) should be collected"
    );
}
