// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::SolveResult;

use super::*;
use crate::AYEncoder;

/// `m.get(3)` on a non-Seq receiver in a non-Bool context dispatches
/// to fmap_lookup (Int-sorted UF). UNSAT dual with equality constraint.
#[test]
#[timeout(30000)]
fn fmap_lookup_via_encode_pure_int_unsat_dual() {
    let mut encoder = AYEncoder::new();

    // m.get(3) — non-Seq receiver, dispatches to fmap lookup path
    let get_expr = method_call(var("m"), "get", vec![int(3)]);

    let term1 = encoder
        .encode_pure(&get_expr)
        .expect("m.get(3) should encode via fmap path");

    let term2 = encoder
        .encode_pure(&get_expr)
        .expect("second m.get(3) should encode");

    // Assert m.get(3) == 42 AND m.get(3) != 42 → UNSAT
    let forty_two = encoder.solver.int_const(42);
    let eq_42 = encoder.solver.eq(term1, forty_two);
    encoder.solver.assert_term(eq_42);

    let forty_two_2 = encoder.solver.int_const(42);
    let eq_42_2 = encoder.solver.eq(term2, forty_two_2);
    let neq_42 = encoder.solver.not(eq_42_2);
    encoder.solver.assert_term(neq_42);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "m.get(3) == 42 AND m.get(3) != 42 should be UNSAT, got: {result:?}"
    );
}

/// `m.contains(7)` on a non-Seq receiver dispatches to fmap_contains.
#[test]
#[timeout(30000)]
fn fmap_contains_via_encode_pure_bool_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let contains_expr = method_call(var("m"), "contains", vec![int(7)]);

    let term1 = encoder
        .encode_pure(&contains_expr)
        .expect("m.contains(7) should encode via fmap path");

    let term2 = encoder
        .encode_pure(&contains_expr)
        .expect("second m.contains(7) should encode");

    encoder.solver.assert_term(term1);
    let not_term = encoder.solver.not(term2);
    encoder.solver.assert_term(not_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "m.contains(7) AND NOT m.contains(7) should be UNSAT, got: {result:?}"
    );
}

/// `m.len()` UNSAT dual: fmap_len(m) == 5 AND fmap_len(m) != 5 is UNSAT.
/// Strengthens the existing fmap_len test (#1685 tautological pattern fix).
#[test]
#[timeout(30000)]
fn fmap_len_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let len_expr = method_call(var("m"), "len", vec![]);

    let term1 = encoder
        .encode_pure(&len_expr)
        .expect("m.len() should encode via fmap path");

    let term2 = encoder
        .encode_pure(&len_expr)
        .expect("second m.len() should encode");

    // Assert len(m) == 5 AND len(m) != 5 → UNSAT
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
        "fmap_len(m) == 5 AND fmap_len(m) != 5 should be UNSAT, got: {result:?}"
    );
}

/// `m.insert(k, v)` UNSAT dual: fmap_insert returns a deterministic
/// FMap-sorted UF. Same args must yield same result.
#[test]
#[timeout(30000)]
fn fmap_insert_unsat_dual() {
    let mut encoder = AYEncoder::new();

    let insert_expr = method_call(var("m"), "insert", vec![int(1), int(42)]);

    let term1 = encoder
        .encode_pure(&insert_expr)
        .expect("m.insert(1, 42) should encode via fmap path");

    let term2 = encoder
        .encode_pure(&insert_expr)
        .expect("second m.insert(1, 42) should encode");

    // fmap_insert returns FMap sort (#2059). Two identical calls must yield
    // the same FMap term — asserting term1 != term2 must be UNSAT.
    let neq = encoder.solver.neq(term1, term2);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_insert(m,1,42) != fmap_insert(m,1,42) should be UNSAT, got: {result:?}"
    );
}
