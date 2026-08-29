// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::SolveResult;

use super::*;
use crate::AYEncoder;

/// fset_peek UNSAT dual: peek(s) is a deterministic UF.
/// Same argument must yield same result.
#[test]
#[timeout(30000)]
fn fset_peek_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let peek_expr = method_call(var("s"), "peek", vec![]);

    let term1 = encoder
        .encode_pure(&peek_expr)
        .expect("s.peek() should encode");

    let term2 = encoder
        .encode_pure(&peek_expr)
        .expect("second s.peek() should encode");

    // Assert peek(s) == 7 AND peek(s) != 7 → UNSAT
    let seven = encoder.solver.int_const(7);
    let eq_7 = encoder.solver.eq(term1, seven);
    encoder.solver.assert_term(eq_7);

    let seven_2 = encoder.solver.int_const(7);
    let eq_7_2 = encoder.solver.eq(term2, seven_2);
    let neq_7 = encoder.solver.not(eq_7_2);
    encoder.solver.assert_term(neq_7);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_peek(s) == 7 AND fset_peek(s) != 7 should be UNSAT, got: {result:?}"
    );
}

/// fset_remove UNSAT dual: remove(s, 5) is a deterministic UF.
#[test]
#[timeout(30000)]
fn fset_remove_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let remove_expr = method_call(var("s"), "remove", vec![int(5)]);

    let term1 = encoder
        .encode_pure(&remove_expr)
        .expect("s.remove(5) should encode");

    let term2 = encoder
        .encode_pure(&remove_expr)
        .expect("second s.remove(5) should encode");

    // Assert remove(s,5) == 10 AND remove(s,5) != 10 → UNSAT
    let ten = encoder.solver.int_const(10);
    let eq_10 = encoder.solver.eq(term1, ten);
    encoder.solver.assert_term(eq_10);

    let ten_2 = encoder.solver.int_const(10);
    let eq_10_2 = encoder.solver.eq(term2, ten_2);
    let neq_10 = encoder.solver.not(eq_10_2);
    encoder.solver.assert_term(neq_10);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_remove(s,5) == 10 AND fset_remove(s,5) != 10 should be UNSAT, got: {result:?}"
    );
}

/// fset_intersection UNSAT dual: intersection(s, t) is deterministic.
#[test]
#[timeout(30000)]
fn fset_intersection_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let inter_expr = method_call(var("s"), "intersection", vec![var("t")]);

    let term1 = encoder
        .encode_pure(&inter_expr)
        .expect("s.intersection(t) should encode");

    let term2 = encoder
        .encode_pure(&inter_expr)
        .expect("second s.intersection(t) should encode");

    let three = encoder.solver.int_const(3);
    let eq_3 = encoder.solver.eq(term1, three);
    encoder.solver.assert_term(eq_3);

    let three_2 = encoder.solver.int_const(3);
    let eq_3_2 = encoder.solver.eq(term2, three_2);
    let neq_3 = encoder.solver.not(eq_3_2);
    encoder.solver.assert_term(neq_3);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_intersection(s,t) == 3 AND fset_intersection(s,t) != 3 should be UNSAT, got: {result:?}"
    );
}

/// fset_difference UNSAT dual: difference(s, t) is deterministic.
#[test]
#[timeout(30000)]
fn fset_difference_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let diff_expr = method_call(var("s"), "difference", vec![var("t")]);

    let term1 = encoder
        .encode_pure(&diff_expr)
        .expect("s.difference(t) should encode");

    let term2 = encoder
        .encode_pure(&diff_expr)
        .expect("second s.difference(t) should encode");

    let four = encoder.solver.int_const(4);
    let eq_4 = encoder.solver.eq(term1, four);
    encoder.solver.assert_term(eq_4);

    let four_2 = encoder.solver.int_const(4);
    let eq_4_2 = encoder.solver.eq(term2, four_2);
    let neq_4 = encoder.solver.not(eq_4_2);
    encoder.solver.assert_term(neq_4);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_difference(s,t) == 4 AND fset_difference(s,t) != 4 should be UNSAT, got: {result:?}"
    );
}

/// fset_len UNSAT dual: len(s) is a deterministic UF (Int-sorted).
/// Same argument must yield the same result. This is the missing dispatch
/// test for the "len" arm added in #2209 — prior to this test, fset_len
/// was only exercised via manual UF setup in algorithm_audit tests.
#[test]
#[timeout(30000)]
fn fset_len_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let len_expr = method_call(var("s"), "len", vec![]);

    let term1 = encoder
        .encode_pure(&len_expr)
        .expect("s.len() should encode via fset_len path");

    let term2 = encoder
        .encode_pure(&len_expr)
        .expect("second s.len() should encode");

    // Assert len(s) == 5 AND len(s) != 5 → UNSAT
    let five = encoder.solver.int_const(5);
    let eq_5 = encoder.solver.eq(term1, five);
    encoder.solver.assert_term(eq_5);

    let five_2 = encoder.solver.int_const(5);
    let eq_5_2 = encoder.solver.eq(term2, five_2);
    let neq_5 = encoder.solver.not(eq_5_2);
    encoder.solver.assert_term(neq_5);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_len(s) == 5 AND fset_len(s) != 5 should be UNSAT, got: {result:?}"
    );
}

/// fset_is_empty UNSAT dual: is_empty(s) AND NOT is_empty(s) is UNSAT.
/// Strengthens the existing is_ok-only test.
#[test]
#[timeout(30000)]
fn fset_is_empty_bool_contradiction_unsat() {
    let mut encoder = AYEncoder::new();

    let empty_expr = method_call(var("s"), "is_empty", vec![]);

    let term1 = encoder
        .encode_pure(&empty_expr)
        .expect("s.is_empty() should encode");

    let term2 = encoder
        .encode_pure(&empty_expr)
        .expect("second s.is_empty() should encode");

    // is_empty(s) AND NOT is_empty(s) → UNSAT
    encoder.solver.assert_term(term1);
    let not_term = encoder.solver.not(term2);
    encoder.solver.assert_term(not_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fset_is_empty(s) AND NOT fset_is_empty(s) should be UNSAT, got: {result:?}"
    );
}
