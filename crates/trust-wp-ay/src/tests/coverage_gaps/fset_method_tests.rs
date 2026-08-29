// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::SolveResult;

use super::*;
use crate::AYEncoder;

/// `s.contains(5)` on a non-Seq receiver dispatches to fset_contains
/// (Bool-sorted UF). Encoding twice and asserting the conjunction with
/// its negation proves the term participates in Boolean reasoning.
#[test]
#[timeout(30000)]
fn fset_contains_via_encode_pure_bool_unsat_dual() {
    let mut encoder = AYEncoder::new();

    // s.contains(5) — `s` is not a known Seq, so dispatch goes to fset path.
    let contains_expr = method_call(var("s"), "contains", vec![int(5)]);

    let term1 = encoder
        .encode_pure(&contains_expr)
        .expect("s.contains(5) should encode via fset path");

    let term2 = encoder
        .encode_pure(&contains_expr)
        .expect("second s.contains(5) should encode");

    // Assert contains(s,5) AND NOT contains(s,5) → UNSAT
    encoder.solver.assert_term(term1);
    let not_term = encoder.solver.not(term2);
    encoder.solver.assert_term(not_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "s.contains(5) AND NOT s.contains(5) should be UNSAT, got: {result:?}"
    );
}

/// `s.is_empty()` on a non-Seq receiver dispatches to fset.
///
/// Strengthened (#1685): now verifies the term is Bool-sorted by checking
/// that asserting it AND its negation yields UNSAT (Boolean contradiction).
#[test]
#[timeout(30000)]
fn fset_is_empty_via_encode_pure_bool_contradiction() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("s"), "is_empty", vec![]);
    let term1 = encoder
        .encode_pure(&expr)
        .expect("s.is_empty() should encode via fset path");
    let term2 = encoder
        .encode_pure(&expr)
        .expect("second s.is_empty() should encode");

    // is_empty(s) AND NOT is_empty(s) → UNSAT (proves Bool participation)
    encoder.solver.assert_term(term1);
    let neg = encoder.solver.not(term2);
    encoder.solver.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "fset_is_empty(s) AND NOT fset_is_empty(s) should be UNSAT"
    );
}
