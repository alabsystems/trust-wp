// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Bool-sorted view identity: b@ == b when b has a Bool sort hint.
///
/// Before #836, view identity was only asserted for Int-sorted views.
/// A Bool variable referenced as both b and b@ would be treated as
/// independent SMT variables, making valid properties unprovable.
/// Part of #836
#[test]
#[timeout(30000)]
fn test_bool_view_identity_asserted() {
    let mut encoder = AYEncoder::new();

    // Register Bool sort hint for variable b
    // (simulates b appearing in a Bool context like Not(View(Var("b"))))
    let hint_expr = not(view(var("b")));
    encoder.register_sort_hints(&[hint_expr]);

    // Encode b@ — should create b_view with Bool sort
    let b_view_term = encoder
        .encode_pure(&view(var("b")))
        .expect("b@ should encode");

    // Encode b — should create b with Bool sort (from base_name fallback)
    let b_term = encoder.encode_pure(&var("b")).expect("b should encode");

    // View identity should have been asserted: b == b_view.
    // If identity was asserted, then (b != b_view) is UNSAT.
    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(b_term, b_view_term);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "b@ must equal b when b has Bool sort hint (#836)"
    );
}

/// Final scalar view identity: (^x)@ == ^x.
///
/// Regression for #1075: final-view variables were left unconstrained
/// (`final_x_view` independent from `x_final`), producing spurious
/// counterexamples like `(^r)@ != ^r` in simple postconditions.
#[test]
#[timeout(30000)]
fn test_final_scalar_view_identity_asserted() {
    let mut encoder = AYEncoder::new();

    let final_view_term = encoder
        .encode_pure(&view(final_expr(var("x"))))
        .expect("(^x)@ should encode");
    let final_term = encoder
        .encode_pure(&final_expr(var("x")))
        .expect("^x should encode");

    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(final_term, final_view_term);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "(^x)@ must equal ^x for scalar views"
    );
}
