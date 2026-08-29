// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// infer_expr_sort tests for Let variant
// =============================================================================

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_with_bool_body() {
    // let x = 0 in (x > 0) => sort is Bool (from body)
    let expr = let_bind("x", int(0), gt(var("x"), int(0)));
    assert_eq!(infer_expr_sort(&expr), Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_with_int_body() {
    // let x = 0 in x + 1 => sort is Int (from body)
    let expr = let_bind("x", int(0), add(var("x"), int(1)));
    assert_eq!(infer_expr_sort(&expr), Sort::Int);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_nested_let() {
    // let x = 0 in (let y = 1 in x > y) => sort is Bool
    let inner_let = let_bind("y", int(1), gt(var("x"), var("y")));
    let expr = let_bind("x", int(0), inner_let);
    assert_eq!(infer_expr_sort(&expr), Sort::Bool);
}

// =============================================================================
// Cross-variant interaction: Let + Bool context
// =============================================================================

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_not_of_let() {
    // !(let b = x in b) => collect_var_names_as_bool should find variables
    // through the Let. The Not triggers collect_var_names_as_bool on the inner
    // Let, which should recurse into the body (not the value).
    let let_expr = let_bind("b", var("x"), var("b"));
    let expr = not(let_expr);
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    // "b" is the leaf var found by collect_var_names_as_bool through Let.body
    assert!(
        names.contains("b"),
        "Not(Let(..., body=Var(b))) should find b as Bool"
    );
    // "x" appears in the Let value, NOT the body. collect_var_names_as_bool
    // deliberately does NOT recurse into value (only body inherits context).
    assert!(
        !names.contains("x"),
        "Let value var should not be propagated as Bool by collect_var_names_as_bool"
    );
}

// =============================================================================
// Cross-variant interaction: Let + Seq context
// =============================================================================

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_let_equality_propagation() {
    // let s = push_back(v@, x) in (w@ == s) => w@ should NOT be Seq
    // because the syntactic walker doesn't track let-binding semantics.
    let push = method_call(view(var("v")), "push_back", vec![var("x")]);
    let body = eq(view(var("w")), var("s"));
    let expr = let_bind("s", push, body);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    // The push_back in the Let value should register v_view
    assert!(
        names.contains("v_view"),
        "push_back receiver in Let value should be found"
    );
    // Equality propagation in the body should NOT find w_view because
    // var("s") is not a Seq-producing expression (it's a plain Var).
    // This is a known limitation of the syntactic walker.
    assert!(
        !names.contains("w_view"),
        "Syntactic walker should not propagate Seq through Let binding"
    );
}

// =============================================================================
// Match expression coverage (self-audit finding 2e/2f/2g)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_match_arms() {
    // match s { _ => !x } => x is Bool inside match arm body
    let expr = match_expr(var("s"), vec![(Pattern::Wildcard, not(var("x")))]);
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside Match arm body should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_var_names_through_match_scrutinee() {
    // match (!x) { _ => 0 } => x is Bool inside scrutinee
    let expr = match_expr(not(var("x")), vec![(Pattern::Wildcard, int(0))]);
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside Match scrutinee should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_match_arm() {
    // match s { _ => v@.len() } => v_view is Seq
    let expr = match_expr(
        var("s"),
        vec![(
            Pattern::Wildcard,
            method_call(view(var("v")), "len", vec![]),
        )],
    );
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method in Match arm body should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_with_bool_arm() {
    // match s { _ => (x > 0) } => sort is Bool (from first arm body)
    let expr = match_expr(var("s"), vec![(Pattern::Wildcard, gt(var("x"), int(0)))]);
    assert_eq!(infer_expr_sort(&expr), Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_with_int_arm() {
    // match s { _ => x + 1 } => sort is Int (from first arm body)
    let expr = match_expr(var("s"), vec![(Pattern::Wildcard, add(var("x"), int(1)))]);
    assert_eq!(infer_expr_sort(&expr), Sort::Int);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_method_invariant_bool() {
    // x.invariant() is a Bool predicate method.
    let expr = method_call(var("x"), "invariant", vec![]);
    assert_eq!(infer_expr_sort(&expr), Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_var_with_seq_annotation() {
    // Seq-annotated variables now correctly infer as Seq sort (#1805).
    // Previous behavior (Sort::Int) caused mk_eq sort panics when
    // Seq-annotated vars were compared with actual Seq terms.
    let expr = var_with_sort("s", ExprSort::Seq);
    assert_eq!(infer_expr_sort(&expr), Sort::seq(Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_set_on_seq_receiver_returns_seq() {
    let expr = method_call(view(var("v")), "set", vec![int(0), int(1)]);
    assert_eq!(infer_expr_sort(&expr), Sort::seq(Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_set_on_non_seq_receiver_stays_int() {
    let expr = method_call(var("mapping"), "set", vec![int(0), int(1)]);
    assert_eq!(infer_expr_sort(&expr), Sort::Int);
}

// =============================================================================
// infer_expr_sort: Let value vs body sort distinction (self-audit finding 2d)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_value_sort_ignored() {
    // let x = (a > b) in x + 1 => sort is Int (body), not Bool (value)
    // Verifies that infer_expr_sort uses the body's sort, not the value's.
    let expr = let_bind("x", gt(var("a"), var("b")), add(var("x"), int(1)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Let sort should come from body, not value"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_int_value_bool_body() {
    // let x = 42 in (x > 0) => sort is Bool (body), not Int (value)
    let expr = let_bind("x", int(42), gt(var("x"), int(0)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Let sort should come from body, not value"
    );
}

// =============================================================================
// infer_expr_sort: View sort inference gap (#1096)
// =============================================================================

/// View(@) recurses into inner expression sort — identity for scalars.
/// Reverted from #2003 unconditional Seq return which caused 8 regressions (#2057).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_view_recurses_to_inner_sort() {
    // View(a > b) — inner is Bool, View recurses → Bool (#2057)
    let expr = view(gt(var("a"), var("b")));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "View(@) recurses into inner sort — Bool comparison stays Bool (#2057)"
    );
    // View(Var("x")) — inner is Var without annotation → Int (default)
    assert_eq!(
        infer_expr_sort(&view(var("x"))),
        Sort::Int,
        "View(@) on unannotated Var defaults to Int (scalar identity)"
    );
}

// =============================================================================
// is_definitely_non_bool: View wrapper gap (sibling of #1096)
// =============================================================================

/// is_definitely_non_bool: Old/Deref/Final/View all recurse into inner.
/// View recurses like Old/Deref/Final — identity for scalars (#2057, reverts #2003).
#[test]
#[timeout(30000)]
fn test_is_definitely_non_bool_wrappers() {
    use crate::encoder::sort_context::is_definitely_non_bool;

    // Old/Deref/Final recurse: Int(42) is definitively non-Bool
    assert!(
        is_definitely_non_bool(&old(int(42))),
        "Old(Int) should be definitively non-Bool"
    );
    assert!(
        is_definitely_non_bool(&deref(int(42))),
        "Deref(Int) should be definitively non-Bool"
    );
    assert!(
        is_definitely_non_bool(&final_expr(int(42))),
        "Final(Int) should be definitively non-Bool"
    );

    // View recurses like Old/Deref/Final (#2057)
    assert!(
        is_definitely_non_bool(&view(int(42))),
        "View(Int) should be definitively non-Bool"
    );
    assert!(
        !is_definitely_non_bool(&view(PureExpr::Bool(true))),
        "View(Bool) recurses — Bool inner is not definitively non-Bool (#2057)"
    );
}

/// Old(Bool(true)) is not definitively non-Bool — verify the recursion
/// correctly reports false for Bool inner.
#[test]
#[timeout(30000)]
fn test_is_definitely_non_bool_wrapper_with_bool_inner() {
    use crate::encoder::sort_context::is_definitely_non_bool;

    assert!(
        !is_definitely_non_bool(&old(PureExpr::Bool(true))),
        "Old(Bool) should not be definitively non-Bool"
    );
    assert!(
        !is_definitely_non_bool(&deref(PureExpr::Bool(true))),
        "Deref(Bool) should not be definitively non-Bool"
    );
    assert!(
        !is_definitely_non_bool(&final_expr(PureExpr::Bool(true))),
        "Final(Bool) should not be definitively non-Bool"
    );
}

// =============================================================================
