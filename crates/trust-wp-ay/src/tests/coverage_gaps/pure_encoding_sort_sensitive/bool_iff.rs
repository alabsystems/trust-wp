// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Bool iff encoding for Eq/Ne ──────────────────────────────────────

/// Bool Eq uses iff encoding: `(x > 0) == (y > 0)`.
/// x=1, y=-1: left true, right false, asserting Eq is UNSAT.
#[test]
#[timeout(30000)]
fn eq_bool_both_sides_uses_iff_encoding() {
    let mut encoder = AYEncoder::new();

    let expr = eq(gt(var("x"), int(0)), gt(var("y"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool==Bool should encode with iff");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let y = encoder.get_or_declare_var("y", Sort::Int).expect("y");
    let one = encoder.solver.int_const(1);
    let x_eq = encoder.solver.eq(x, one);
    encoder.solver.assert_term(x_eq);
    let neg_one = encoder.solver.int_const(-1);
    let y_eq = encoder.solver.eq(y, neg_one);
    encoder.solver.assert_term(y_eq);

    encoder.solver.assert_term(term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=1, y=-1, (x>0)==(y>0) must be UNSAT — true != false"
    );
}

/// Bool Ne is negated iff: x=1, y=2: both >0, Ne is false.
#[test]
#[timeout(30000)]
fn ne_bool_both_sides_negated_iff() {
    let mut encoder = AYEncoder::new();

    let expr = ne(gt(var("x"), int(0)), gt(var("y"), int(0)));
    let term = encoder
        .encode_pure(&expr)
        .expect("Bool!=Bool should encode");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let y = encoder.get_or_declare_var("y", Sort::Int).expect("y");
    let one = encoder.solver.int_const(1);
    let x_eq = encoder.solver.eq(x, one);
    encoder.solver.assert_term(x_eq);
    let two = encoder.solver.int_const(2);
    let y_eq = encoder.solver.eq(y, two);
    encoder.solver.assert_term(y_eq);

    encoder.solver.assert_term(term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=1, y=2, (x>0)!=(y>0) must be UNSAT — both true"
    );
}
