// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_view_of_deref_succeeds() {
    // (*v)@ - view of deref should succeed and produce v_current_view (Part of #329)
    let mut encoder = AYEncoder::new();

    let expr = view(deref(var("v")));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View of deref (*v)@ should succeed: {:?}",
        result.as_ref().err()
    );
    // Variable name should be v_current_view
    assert!(
        encoder.vars_for_test().contains_key("v_current_view"),
        "Should create v_current_view variable"
    );
    let term = result.expect("view of deref should encode");
    let expected = *encoder
        .vars_for_test()
        .get("v_current_view")
        .expect("v_current_view should be registered");
    let not_eq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded view-of-deref term should be exactly v_current_view"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_view_of_final_of_deref_succeeds() {
    // (^(*v))@ - view of final of deref should succeed (Part of #329)
    // Uses "final_{inner}_view" format for View(Final(..))
    let mut encoder = AYEncoder::new();

    let expr = view(final_expr(deref(var("v"))));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View of final of deref (^(*v))@ should succeed: {result:?}"
    );
    // Variable name should be final_v_current_view (final_{inner}_view format)
    assert!(
        encoder.vars_for_test().contains_key("final_v_current_view"),
        "Should create final_v_current_view variable"
    );
    let term = result.expect("view of final of deref should encode");
    let expected = *encoder
        .vars_for_test()
        .get("final_v_current_view")
        .expect("final_v_current_view should be registered");
    let not_eq = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(not_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded view-of-final-of-deref term should be exactly final_v_current_view"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_view_of_binop_succeeds() {
    // (x + y)@ - view of Int-sorted arithmetic expression is identity (#858).
    // Scalars don't need the `view` UF wrapper — the model conversion is a no-op.
    let mut encoder = AYEncoder::new();

    let expr = view(add(var("x"), var("y")));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View of arithmetic expression should encode successfully: {result:?}"
    );
    // Int-sorted view is identity: logic_view should NOT be registered (#858).
    // Check prefix to catch sort-suffixed placeholder keys too (#2274).
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("logic_view")),
        "Scalar view is identity — logic_view should not be registered, got: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_view_of_logic_fn_call_succeeds() {
    // f(x)@ - view of Int-sorted logic function call is identity (#858).
    // Generic LogicFnCall infers as Int, so view is a no-op.
    let mut encoder = AYEncoder::new();

    let expr = view(logic_fn_call("some_fn", vec![var("x")]));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View of logic fn call should encode successfully: {result:?}"
    );
    // Int-sorted view is identity: logic_view should NOT be registered (#858).
    // Check prefix to catch sort-suffixed placeholder keys too (#2274).
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("logic_view")),
        "Scalar view is identity — logic_view should not be registered, got: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    // The inner logic function should still be registered (placeholder-keyed
    // with sort suffix since #2274)
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("logic_some__fn")),
        "Inner logic fn call should still be registered, got: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_view_of_method_call_succeeds() {
    // v@.len()@ - view of Int-sorted method call (len) is identity (#858).
    // The inner View(Var("v")) uses the named-var fast path (producing v_view).
    // The outer View wraps a MethodCall("len") which infers as Int, so
    // the view is a no-op — logic_view is not registered.
    let mut encoder = AYEncoder::new();

    let expr = view(method_call(view(var("v")), "len", vec![]));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View of method call should encode successfully: {result:?}"
    );
    // Int-sorted view (len returns Int) is identity: no logic_view (#858).
    // Check prefix to catch sort-suffixed placeholder keys too (#2274).
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|k| k.starts_with("logic_view")),
        "Scalar view is identity — logic_view should not be registered, got: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// View of `capacity()` uses scalar identity — no `logic_fn_placeholder:view`.
/// Regression for 09_capacity (#994 Slice 3): capacity() is Int-returning,
/// so View wrapping it should take the fast path, not route through the
/// placeholder-based `apply_logic_fn("view", ...)` path that crashes on
/// sort mismatch.
#[test]
#[timeout(30000)]
fn test_encode_view_of_capacity_uses_scalar_path() {
    let mut encoder = AYEncoder::new();

    let expr = view(method_call(view(var("v")), "capacity", vec![]));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View of capacity() should encode successfully: {result:?}"
    );
    assert!(
            !encoder
                .decls()
                .logic_func_names()
                .any(|k| k.starts_with("logic_view")
                    || k.contains("placeholder") && k.contains("view")),
            "capacity() is scalar Int — view should use identity, not placeholder, got: {:?}",
            encoder.decls().logic_func_names().collect::<Vec<_>>()
        );
}

#[test]
#[timeout(30000)]
fn test_simple_view_succeeds() {
    // v@ should succeed (regression test)
    let mut encoder = AYEncoder::new();

    let expr = view(var("v"));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Simple view should succeed: {:?}",
        result.as_ref().err()
    );

    // Semantic: v@ creates v_view variable
    assert!(
        encoder.vars_for_test().contains_key("v_view"),
        "View should create v_view variable"
    );
    // Semantic check: encoded term must be the canonical view variable.
    let term = result.unwrap();
    let expected = *encoder
        .vars_for_test()
        .get("v_view")
        .expect("v_view should be registered");
    let neq_term = encoder.solver.neq(term, expected);
    encoder.solver.assert_term(neq_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "encoded view term should be exactly v_view"
    );
}

#[test]
#[timeout(30000)]
fn test_final_view_succeeds() {
    // (^v)@ should succeed - final view of simple variable
    let mut encoder = AYEncoder::new();

    let expr = view(final_expr(var("v")));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Final view of simple var should succeed: {:?}",
        result.as_ref().err()
    );

    // Semantic: (^v)@ creates final_v_view; verify the variable was created
    assert!(
        encoder.vars_for_test().contains_key("final_v_view"),
        "Final view should create final_v_view variable"
    );
    // Verify the term is usable in a solver query
    let term = result.unwrap();
    let zero = encoder.solver.int_const(0);
    let eq_term = encoder.solver.eq(term, zero);
    encoder.solver.assert_term(eq_term);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "final_v_view == 0 should be SAT (unconstrained variable), got {result:?}"
    );
}

/// Test that view of a Seq-sorted complex expression applies the `view` UF.
///
/// `(v@.push_back(x))@` — the inner `push_back` returns Seq sort.
/// View is identity for logical collection sorts (Seq, FMap) because these
/// ARE the deep model. The outer View returns the inner Seq term directly,
/// preserving sort and avoiding opaque UF placeholders that break axiom
/// trigger matching in ay-dpll's single-round E-matching. (#2116)
///
/// Part of #1512, updated for #2116 Seq-view identity semantics.
#[test]
#[timeout(30000)]
fn test_encode_view_of_seq_returning_method_applies_view_uf() {
    let mut encoder = AYEncoder::new();

    // v@.push_back(x) returns Seq sort
    let push_back = method_call(view(var("v")), "push_back", vec![var("x")]);
    // View of that Seq-returning expression should return the inner term
    let expr = view(push_back.clone());

    let term = encoder
        .encode_pure(&expr)
        .expect("View of Seq-returning push_back should encode");
    let inner_term = encoder
        .encode_pure(&push_back)
        .expect("push_back should encode");
    // View of Seq is identity: same term as the inner expression
    assert_eq!(
        term, inner_term,
        "View of Seq-returning method must be identity (same term)"
    );
    assert_eq!(
        encoder.solver.get_sort(term),
        encoder.sort_from_expr_sort(ExprSort::Seq),
        "View of a Seq-returning method must stay Seq-sorted"
    );
}

/// Test that view of a `seq!` constructor (LogicFnCall("seq")) applies the view UF.
///
/// `seq![1, 2, 3]@` — the seq constructor returns Seq sort, so the outer
/// View must apply `logic_view`. This is a second path to view.rs:144-147.
///
/// Part of #1512, updated for #2116 Seq-view identity semantics.
#[test]
#[timeout(30000)]
fn test_encode_view_of_seq_constructor_applies_view_uf() {
    let mut encoder = AYEncoder::new();

    // seq!(1, 2, 3) returns Seq sort
    let seq_expr = logic_fn_call("seq", vec![int(1), int(2), int(3)]);
    let expr = view(seq_expr);

    let term = encoder
        .encode_pure(&expr)
        .expect("View of seq constructor should preserve Seq sort");
    // View of Seq is identity (#2116): Seq IS the deep model, so viewing
    // it again is a no-op. No logic_view UF should be registered.
    assert_eq!(
        encoder.solver.get_sort(term),
        encoder.sort_from_expr_sort(ExprSort::Seq),
        "View of a seq constructor must stay Seq-sorted"
    );
    let logic_view_names: Vec<_> = encoder
        .decls()
        .logic_func_names()
        .filter(|name| name.starts_with("logic_view"))
        .collect();
    assert!(
        logic_view_names.is_empty(),
        "Seq-view identity should NOT register logic_view UF (#2116), got: {:?}",
        logic_view_names
    );
}

/// Regression for #994, updated for #2116: `view(seq_empty())` must return
/// the seq_empty term directly (identity) with Seq sort.
#[test]
#[timeout(30000)]
fn test_encode_view_of_seq_empty_uses_seq_return_sort() {
    let mut encoder = AYEncoder::new();

    let inner_expr = logic_fn_call("seq_empty", vec![]);
    let term = encoder
        .encode_pure(&view(inner_expr.clone()))
        .expect("View of seq_empty() should encode");
    let inner_term = encoder
        .encode_pure(&inner_expr)
        .expect("seq_empty should encode");
    // View of Seq is identity (#2116)
    assert_eq!(
        term, inner_term,
        "View of seq_empty() must be identity (same term)"
    );
    assert_eq!(
        encoder.solver.get_sort(term),
        encoder.sort_from_expr_sort(ExprSort::Seq),
        "View of seq_empty() must stay Seq-sorted"
    );
}
