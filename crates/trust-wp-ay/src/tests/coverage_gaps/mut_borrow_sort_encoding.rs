// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Coverage gap tests for MutBorrow Bool-sort encoding paths.
//!
//! Previous MutBorrow tests (`basic.rs:test_encode_mut_borrow`) only exercised
//! Int-sorted expressions. These tests cover the `eq_or_iff` path at
//! `sep_logic.rs:518-519` which uses `iff` (instead of `eq`) when
//! the MutBorrow variable has Bool sort.

use std::sync::Arc;

use super::*;

/// MutBorrow with Bool-sorted expressions uses `iff` (not `eq`) for
/// constraint encoding to avoid ay-dpll sort mismatches (#1179).
///
/// Exercises sep_logic.rs:518-519: the `eq_or_iff` path with Bool sort.
///
/// Uses `gt(var("x"), int(0))` as current — `infer_expr_sort` returns Bool
/// for comparison operators, so `b_current` is pre-declared as Bool.
#[test]
#[timeout(30000)]
fn test_encode_mut_borrow_bool_sort_uses_iff() {
    let mut encoder = AYEncoder::new();

    // MutBorrow where both current and final are Bool-sorted:
    // current = (x > 0), final = NOT(x > 0)
    // infer_expr_sort(Gt(..)) = Sort::Bool
    let formula = Formula::MutBorrow {
        var: "b".to_string(),
        current: Arc::new(gt(var("x"), int(0))),
        final_val: Arc::new(not(gt(var("x"), int(0)))),
        id: Arc::new(int(0)),
    };

    let term = encoder.encode(&formula).unwrap();
    encoder.assert_term(term);

    // Should be SAT — x can be any value
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Bool MutBorrow (b_current = x>0, b_final = !(x>0)) should be SAT"
    );

    // Verify the Bool sort was used for the MutBorrow variables
    assert_eq!(
        encoder.var_sorts_for_test().get("b_current").cloned(),
        Some(Sort::Bool),
        "b_current should have Bool sort when current is a comparison"
    );
    assert_eq!(
        encoder.var_sorts_for_test().get("b_final").cloned(),
        Some(Sort::Bool),
        "b_final should have Bool sort when final is a negated comparison"
    );
}

/// MutBorrow with Int current but Bool final creates mixed-sort constraints.
/// The encoder must use `eq` for the Int constraint and `iff` for the Bool one.
///
/// Semantic verification: with x=5, v_final should equal (5 > 0) = true.
#[test]
#[timeout(30000)]
fn test_encode_mut_borrow_mixed_sort_int_and_bool() {
    let mut encoder = AYEncoder::new();

    // current = x (Int-sorted by default), final = x > 0 (Bool-sorted)
    let formula = Formula::MutBorrow {
        var: "v".to_string(),
        current: Arc::new(var("x")),
        final_val: Arc::new(gt(var("x"), int(0))),
        id: Arc::new(int(1)),
    };

    let term = encoder.encode(&formula).unwrap();
    encoder.assert_term(term);

    // Assert x = 5, then check that v_final = (5 > 0) = true
    let x_var = *encoder.vars_for_test().get("x").expect("x should exist");
    let five = encoder.solver.int_const(5);
    let x_eq_5 = encoder.solver.eq(x_var, five);
    encoder.assert_term(x_eq_5);

    let v_final = *encoder
        .vars_for_test()
        .get("v_final")
        .expect("v_final should exist");
    let neg_v_final = encoder.solver.not(v_final);
    encoder.assert_term(neg_v_final);

    // NOT(v_final) with x=5 should be UNSAT because v_final = (5 > 0) = true
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "v_final should equal (x>0), so NOT(v_final) with x=5 is UNSAT"
    );
}

/// MutBorrow with Bool-sorted expressions should produce correct semantic
/// encoding for the negative case. When current is (x > 10) and we
/// assert x = 3, then b_current should be false.
#[test]
#[timeout(30000)]
fn test_encode_mut_borrow_bool_negative_case() {
    let mut encoder = AYEncoder::new();

    let formula = Formula::MutBorrow {
        var: "b".to_string(),
        current: Arc::new(gt(var("x"), int(10))),
        final_val: Arc::new(le(var("x"), int(10))),
        id: Arc::new(int(2)),
    };

    let term = encoder.encode(&formula).unwrap();
    encoder.assert_term(term);

    // Assert x = 3
    let x_var = *encoder.vars_for_test().get("x").expect("x should exist");
    let three = encoder.solver.int_const(3);
    let x_eq_3 = encoder.solver.eq(x_var, three);
    encoder.assert_term(x_eq_3);

    // b_current should be false (3 > 10 is false), so asserting b_current
    // should give UNSAT
    let b_current = *encoder
        .vars_for_test()
        .get("b_current")
        .expect("b_current should exist");
    encoder.assert_term(b_current);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "b_current with x=3 and current=(x>10) should be false, so asserting it is UNSAT"
    );
}
