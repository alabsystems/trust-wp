// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── encode_unop tests ────────────────────────────────────────────────

/// Not encoding: NOT(x > 0) with x=5 is false (UNSAT).
#[test]
#[timeout(30000)]
fn unop_not_encoding_semantic() {
    let mut encoder = AYEncoder::new();

    let expr = not(gt(var("x"), int(0)));
    let term = encoder.encode_pure(&expr).expect("NOT should encode");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x, five);
    encoder.solver.assert_term(x_eq);

    encoder.solver.assert_term(term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=5, NOT(x>0) must be UNSAT"
    );
}

/// Neg encoding: -x is encoded as 0 - x.
/// x=3 => -x == -3. NOT(-x == -3) is UNSAT.
#[test]
#[timeout(30000)]
fn unop_neg_encoding_as_zero_minus() {
    let mut encoder = AYEncoder::new();

    let neg_x = neg(var("x"));
    let expr = eq(neg_x, int(-3));
    let term = encoder
        .encode_pure(&expr)
        .expect("Neg should encode as 0-x");

    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let three = encoder.solver.int_const(3);
    let x_eq = encoder.solver.eq(x, three);
    encoder.solver.assert_term(x_eq);

    let neg_term = encoder.solver.not(term);
    encoder.solver.assert_term(neg_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=3, NOT(-x == -3) must be UNSAT"
    );
}

// ── seed_bool_context_hints ──────────────────────────────────────────

/// Not(var("flag")) seeds a Bool hint for "flag".
#[test]
#[timeout(30000)]
fn not_seeds_bool_context_hint_for_inner_var() {
    let mut encoder = AYEncoder::new();

    let expr = not(var("flag"));
    let _term = encoder.encode_pure(&expr).expect("NOT(flag) should encode");

    assert_eq!(
        encoder.var_sort("flag"),
        Some(&Sort::Bool),
        "NOT(var) must seed Bool sort hint via seed_bool_context_hints"
    );
}

/// Ite condition seeds Bool hints for condition variables.
#[test]
#[timeout(30000)]
fn ite_condition_seeds_bool_hint() {
    let mut encoder = AYEncoder::new();

    let expr = ite(var("flag"), int(1), int(2));
    let _term = encoder
        .encode_pure(&expr)
        .expect("ite(flag, 1, 2) should encode");

    assert_eq!(
        encoder.var_sort("flag"),
        Some(&Sort::Bool),
        "Ite condition variable must be seeded as Bool"
    );
}
