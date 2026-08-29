// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Eq/Ne mixed-sort operand encoding ────────────────────────────────

/// Eq with Bool left and non-Bool right: `(x > 0) == flag`.
#[test]
#[timeout(30000)]
fn eq_mixed_bool_left_nonbool_right_encoding() {
    let mut encoder = AYEncoder::new();

    let expr = eq(gt(var("x"), int(0)), var("flag"));
    let term = encoder
        .encode_pure(&expr)
        .expect("mixed Bool/non-Bool Eq should encode");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x, five);
    encoder.solver.assert_term(x_eq);

    let flag = encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("flag");
    let t = encoder.solver.bool_const(true);
    let flag_eq = encoder.solver.eq(flag, t);
    encoder.solver.assert_term(flag_eq);

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=5, flag=true, NOT((x>0)==flag) must be UNSAT"
    );
}

/// Ne with mixed Bool encoding: x=5, flag=true => Ne is false.
#[test]
#[timeout(30000)]
fn ne_mixed_bool_encoding_constrains() {
    let mut encoder = AYEncoder::new();

    let expr = ne(gt(var("x"), int(0)), var("flag"));
    let term = encoder
        .encode_pure(&expr)
        .expect("mixed Bool Ne should encode");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x, five);
    encoder.solver.assert_term(x_eq);

    let flag = encoder
        .get_or_declare_var("flag", Sort::Bool)
        .expect("flag");
    let t = encoder.solver.bool_const(true);
    let flag_eq = encoder.solver.eq(flag, t);
    encoder.solver.assert_term(flag_eq);

    encoder.solver.assert_term(term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=5, flag=true, (x>0)!=flag must be UNSAT — both true"
    );
}

/// Eq with both non-Bool operands uses standard eq.
#[test]
#[timeout(30000)]
fn eq_both_int_uses_standard_eq() {
    let mut encoder = AYEncoder::new();

    let expr = eq(var("x"), int(5));
    let term = encoder.encode_pure(&expr).expect("Int==Int should encode");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x, five);
    encoder.solver.assert_term(x_eq);

    let neg = encoder.solver.not(term);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=5, NOT(x==5) must be UNSAT"
    );
}
