// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// View of a scalar variable asserts identity: x == x_view.
/// Assert x = 5 and x_view != 5 → UNSAT (view identity holds).
#[test]
#[timeout(30000)]
fn test_view_scalar_identity_holds() {
    let mut encoder = AYEncoder::new();

    // Encode View(Var("x")) which triggers assert_view_identity
    let view_expr = view(var("x"));
    let view_term = encoder
        .encode_pure(&view_expr)
        .expect("View(Var(x)) should encode");

    // Set x = 5
    let x_term = *encoder
        .vars_for_test()
        .get("x")
        .expect("x should be declared");
    let five = encoder.solver_mut().int_const(5);
    let x_eq_5 = encoder.solver_mut().eq(x_term, five);
    encoder.assert_term(x_eq_5);

    // Assert view != 5 → should be UNSAT due to view identity
    let view_eq_5 = encoder.solver_mut().eq(view_term, five);
    let view_neq_5 = encoder.solver_mut().not(view_eq_5);
    encoder.assert_term(view_neq_5);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=5 AND view(x)!=5 should be Unsat (view identity asserted)"
    );
}

/// SAT dual: View of a scalar variable — x and view(x) are linked but unconstrained.
/// Assert x = view(x) = 5 → SAT.
#[test]
#[timeout(30000)]
fn test_view_scalar_identity_sat_dual() {
    let mut encoder = AYEncoder::new();

    let view_expr = view(var("x"));
    let view_term = encoder
        .encode_pure(&view_expr)
        .expect("View(Var(x)) should encode");

    // Assert view = 5 (since identity is asserted, x = 5 also holds)
    let five = encoder.solver_mut().int_const(5);
    let view_eq_5 = encoder.solver_mut().eq(view_term, five);
    encoder.assert_term(view_eq_5);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "view(x) = 5 should be Sat (view identity allows this)"
    );
}

/// View identity is asserted only once per base name (idempotent guard).
/// Encoding View(x) twice should not cause solver errors or double assertions.
#[test]
#[timeout(30000)]
fn test_view_identity_idempotent() {
    let mut encoder = AYEncoder::new();

    // Encode View(x) twice
    let view_expr1 = view(var("x"));
    let view_term1 = encoder
        .encode_pure(&view_expr1)
        .expect("first View(x) should encode");
    let view_expr2 = view(var("x"));
    let view_term2 = encoder
        .encode_pure(&view_expr2)
        .expect("second View(x) should encode");

    // Both should resolve to the same term (idempotent)
    let eq = encoder.solver_mut().eq(view_term1, view_term2);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "two view(x) encodings should be equal"
    );

    // UNSAT dual: they can't be different
    let mut encoder2 = AYEncoder::new();
    let v1 = encoder2
        .encode_pure(&view(var("x")))
        .expect("View(x) should encode");
    let v2 = encoder2
        .encode_pure(&view(var("x")))
        .expect("View(x) should encode again");
    let eq_v = encoder2.solver_mut().eq(v1, v2);
    let neq = encoder2.solver_mut().not(eq_v);
    encoder2.assert_term(neq);
    assert!(
        matches!(encoder2.check_sat(), SolveResult::Unsat(_)),
        "two view(x) encodings should never differ — UNSAT expected"
    );
}

/// Nested views should collapse to the original view term rather than creating
/// a fresh `_view_view` placeholder. This matters for collection specs that
/// thread iterator views through `collect()` and produce formulas like `xs@@`.
#[test]
#[timeout(30000)]
fn test_nested_view_reuses_existing_fmap_view_term() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);

    let single_view = encoder
        .encode_pure(&view(var("m")))
        .expect("single FMap view should encode");
    let nested_view = encoder
        .encode_pure(&view(view(var("m"))))
        .expect("nested FMap view should collapse");

    assert_eq!(
        single_view, nested_view,
        "nested FMap view should reuse the original view term"
    );
    assert!(
        !encoder.vars_for_test().contains_key("m_view_view"),
        "nested view collapse must not create a fresh m_view_view variable"
    );
}

/// View over a set-adapter expression keeps a bridge to the underlying term.
#[test]
#[timeout(30000)]
fn test_set_adapter_view_bridge_is_asserted() {
    let mut encoder = AYEncoder::new();

    let adapter_expr = method_call(var("xs"), "intersection", vec![var("ys")]);
    let view_term = encoder
        .encode_pure(&view(adapter_expr.clone()))
        .expect("set-adapter view should encode");
    let raw_term = encoder
        .encode_pure(&adapter_expr)
        .expect("raw set-adapter expression should encode");

    let eq = encoder.solver_mut().eq(view_term, raw_term);
    let neq = encoder.solver_mut().not(eq);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "set-adapter view bridge should make view(expr) equal to expr"
    );
}
