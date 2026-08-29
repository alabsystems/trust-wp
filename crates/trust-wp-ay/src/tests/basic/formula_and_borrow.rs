// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
#[test]
#[timeout(30000)]
fn test_encode_pure_binop_or() {
    // Test BinOp::Or encoding: (x > 0) || (y > 0)
    let mut encoder = AYEncoder::new();
    let x_gt_0 = gt(var("x"), int(0));
    let y_gt_0 = gt(var("y"), int(0));
    let expr = or(x_gt_0, y_gt_0);
    let term = encoder.encode_pure(&expr).unwrap();

    // Semantic: x <= 0 AND y <= 0 should make (x > 0 || y > 0) false
    let x = *encoder.vars_for_test().get("x").unwrap();
    let y = *encoder.vars_for_test().get("y").unwrap();
    let zero = encoder.solver.int_const(0);
    let x_le_0 = encoder.solver.le(x, zero);
    let y_le_0 = encoder.solver.le(y, zero);
    encoder.assert_term(x_le_0);
    encoder.assert_term(y_le_0);
    encoder.assert_term(term); // assert the disjunction is true
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x <= 0 AND y <= 0 AND (x > 0 || y > 0) should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_pure_binop_implies() {
    // Test BinOp::Implies encoding: (x > 0) ==> (x >= 0)
    let mut encoder = AYEncoder::new();
    let x_gt_0 = gt(var("x"), int(0));
    let x_ge_0 = ge(var("x"), int(0));
    let expr = implies(x_gt_0, x_ge_0);
    let term = encoder.encode_pure(&expr).unwrap();

    // Semantic: (x > 0) ==> (x >= 0) is a tautology — its negation should be UNSAT
    let neg = encoder.solver.not(term);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "NOT((x > 0) ==> (x >= 0)) should be UNSAT (tautology)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_formula_true_false() {
    let mut encoder = AYEncoder::new();

    let t = encoder.encode(&Formula::True).unwrap();
    encoder.assert_term(t);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Formula::True should be SAT"
    );

    // New encoder for false test
    let mut encoder2 = AYEncoder::new();
    let f = encoder2.encode(&Formula::False).unwrap();
    encoder2.assert_term(f);
    assert!(
        matches!(encoder2.check_sat(), SolveResult::Unsat(_)),
        "Formula::False should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_formula_or() {
    // Test Formula::Or encoding: true || false -> SAT
    let mut encoder = AYEncoder::new();
    let formula = formula_or(Formula::True, Formula::False);
    let term = encoder.encode(&formula).unwrap();
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "true || false should be SAT"
    );

    // Test false || false -> UNSAT
    let mut encoder2 = AYEncoder::new();
    let formula2 = formula_or(Formula::False, Formula::False);
    let term2 = encoder2.encode(&formula2).unwrap();
    encoder2.assert_term(term2);
    assert!(
        matches!(encoder2.check_sat(), SolveResult::Unsat(_)),
        "false || false should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_formula_implies() {
    // Test Formula::Implies encoding: true ==> true -> SAT
    let mut encoder = AYEncoder::new();
    let formula = formula_implies(Formula::True, Formula::True);
    let term = encoder.encode(&formula).unwrap();
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "true ==> true should be SAT"
    );

    // Test true ==> false -> UNSAT
    let mut encoder2 = AYEncoder::new();
    let formula2 = formula_implies(Formula::True, Formula::False);
    let term2 = encoder2.encode(&formula2).unwrap();
    encoder2.assert_term(term2);
    assert!(
        matches!(encoder2.check_sat(), SolveResult::Unsat(_)),
        "true ==> false should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_old_expression() {
    let mut encoder = AYEncoder::new();

    // old(x) should create old_x variable
    let expr = old(var("x"));
    let _term = encoder.encode_pure(&expr).unwrap();

    // Check that old_x was declared
    assert!(
        encoder.vars_for_test().contains_key("old_x"),
        "old(x) should declare 'old_x' variable; found: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_ite() {
    let mut encoder = AYEncoder::new();

    // if x > 0 then 1 else 0
    let expr = ite(gt(var("x"), int(0)), int(1), int(0));
    let term = encoder.encode_pure(&expr).unwrap();

    // Semantic: when x = 5 (positive), ITE result should be 1
    let x = *encoder.vars_for_test().get("x").unwrap();
    let five = encoder.solver.int_const(5);
    let one = encoder.solver.int_const(1);
    let x_eq_5 = encoder.solver.eq(x, five);
    encoder.assert_term(x_eq_5);
    let eq_one = encoder.solver.eq(term, one);
    let neq_one = encoder.solver.not(eq_one);
    encoder.assert_term(neq_one); // assert result != 1
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x=5, if x>0 then 1 else 0 should equal 1 (negation UNSAT)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_mut_borrow() {
    // Test RustHorn-style mutable borrow encoding
    let mut encoder = AYEncoder::new();

    let formula = Formula::MutBorrow {
        var: "v".to_string(),
        current: Arc::new(var("x")),
        final_val: Arc::new(add(var("x"), int(1))),
        id: Arc::new(int(0)),
    };

    let term = encoder.encode(&formula).unwrap();
    encoder.assert_term(term);

    // Should be SAT (x can be any value)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "MutBorrow with v_final = x + 1 should be SAT"
    );

    // Check that the variables were created
    assert!(
        encoder.vars_for_test().contains_key("v_current"),
        "MutBorrow should declare 'v_current'; found: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
    assert!(
        encoder.vars_for_test().contains_key("v_final"),
        "MutBorrow should declare 'v_final'; found: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
    assert!(
        encoder.vars_for_test().contains_key("x"),
        "MutBorrow body should declare 'x'; found: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
    assert!(
        encoder.vars_for_test().contains_key("v_id"),
        "MutBorrow should declare 'v_id'; found: {:?}",
        encoder.vars_for_test().keys().collect::<Vec<_>>()
    );
}

// ============================================================================
// Coverage gap tests: UnOp::Neg encoding
// ============================================================================
