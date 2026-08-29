// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Test `UnOp::Neg` encoding: negation is encoded as `0 - inner`.
///
/// Exercises encoder.rs:982-984 which was previously untested.
/// Verifies: -5 == -(5) by asserting NOT(-5 == -(5)) is UNSAT.
#[test]
#[timeout(30000)]
fn test_encode_unop_neg() {
    let mut encoder = AYEncoder::new();

    // Encode -(5) and check it equals -5
    let neg_five_via_unop = neg(int(5));
    let neg_five_literal = int(-5);

    let neg_term = encoder.encode_pure(&neg_five_via_unop).unwrap();
    let lit_term = encoder.encode_pure(&neg_five_literal).unwrap();

    // Assert NOT(-(5) == -5) — should be UNSAT (they are equal)
    let eq_term = encoder.solver.eq(neg_term, lit_term);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "UnOp::Neg encoding: -(5) should equal -5"
    );
}

/// Test `UnOp::Neg` with variable: -x + x == 0.
///
/// Verifies that negating a variable and adding it back yields zero.
#[test]
#[timeout(30000)]
fn test_encode_unop_neg_variable() {
    let mut encoder = AYEncoder::new();

    // -x + x should equal 0
    let neg_x = neg(var("x"));
    let sum = add(neg_x, var("x"));
    let zero = int(0);

    let sum_term = encoder.encode_pure(&sum).unwrap();
    let zero_term = encoder.encode_pure(&zero).unwrap();

    // Assert NOT(-x + x == 0) — should be UNSAT
    let eq_term = encoder.solver.eq(sum_term, zero_term);
    let neq = encoder.solver.not(eq_term);
    encoder.solver.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "UnOp::Neg encoding: -x + x should equal 0"
    );
}

/// Regression: `infer_expr_sort` should recurse through Old/Deref/Final wrappers (#544).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_wrapper_recursion() {
    use crate::encoder::infer_expr_sort;

    // Old(BinOp(Eq)) should be Bool, not Int
    let old_eq = old(eq(var("x"), int(0)));
    assert_eq!(
        infer_expr_sort(&old_eq),
        Sort::Bool,
        "Old(Eq(..)) should infer as Bool, not Int"
    );

    // Deref(Bool(true)) should be Bool
    let deref_bool = deref(bool_expr(true));
    assert_eq!(
        infer_expr_sort(&deref_bool),
        Sort::Bool,
        "Deref(Bool(true)) should infer as Bool"
    );

    // Final(UnOp(Not, ...)) should be Bool
    let final_not = final_expr(not(bool_expr(false)));
    assert_eq!(
        infer_expr_sort(&final_not),
        Sort::Bool,
        "Final(Not(..)) should infer as Bool"
    );

    // Old(Deref(Var("x"))) should be Int (Var defaults to Int)
    let old_deref_var = old(deref(var("x")));
    assert_eq!(
        infer_expr_sort(&old_deref_var),
        Sort::Int,
        "Old(Deref(Var)) should infer as Int (Var defaults to Int)"
    );
}

/// Regression: Not(Var("b")) should encode without panic when b is in Bool context (#544).
///
/// Before the Bool pre-scan, Var("b") was always declared as `Sort::Int`.
/// Not(Var("b")) then called `mk_not(Int)` which panicked with
/// "BUG: `mk_not` expects Bool, got Int".
#[test]
#[timeout(30000)]
fn test_encode_not_var_bool_prescan() {
    let mut encoder = AYEncoder::new_pure();

    // Not(Var("b")) — the pre-scan in encode_pure should detect that b needs Bool
    let expr = not(var("b"));
    let term = encoder.encode_pure(&expr).unwrap();

    // Assert Not(b) — should be satisfiable (b = false)
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Not(b) should be SAT (b = false)"
    );
}

/// Strengthening: Not(Var("b")) should conflict with b == true.
#[test]
#[timeout(30000)]
fn test_encode_not_var_bool_prescan_conflict_is_unsat() {
    let mut encoder = AYEncoder::new_pure();

    let expr = not(var("b"));
    let term = encoder.encode_pure(&expr).unwrap();
    let b = *encoder
        .vars_for_test()
        .get("b")
        .expect("b should be declared during Bool pre-scan");
    let b_true = {
        let solver = encoder.solver_mut();
        let t = solver.bool_const(true);
        solver.eq(b, t)
    };

    encoder.assert_term(term);
    encoder.assert_term(b_true);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Not(b) AND b should be UNSAT"
    );
}

/// Regression: Ite(Var("flag"), ...) should encode without panic (#544).
///
/// Before the Bool pre-scan, Var("flag") was always declared as `Sort::Int`.
/// Ite(Var("flag"), ...) then called `mk_ite` with Int condition which panicked
/// with "BUG: `mk_ite` condition must be Bool, got Int".
#[test]
#[timeout(30000)]
fn test_encode_ite_var_condition_bool_prescan() {
    let mut encoder = AYEncoder::new_pure();

    // Ite(Var("flag"), Int(1), Int(0)) — flag must be Bool for ite condition
    let expr = ite(var("flag"), int(1), int(0));
    let term = encoder.encode_pure(&expr).unwrap();

    // Assert ite(flag, 1, 0) > 0 — should be satisfiable (flag = true)
    let zero = encoder.solver_mut().int_const(0);
    let gt_term = encoder.solver_mut().gt(term, zero);
    encoder.assert_term(gt_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "ite(flag, 1, 0) > 0 should be SAT (flag = true)"
    );
}

/// Strengthening: ite(flag, 1, 0) > 0 should conflict with flag == false.
#[test]
#[timeout(30000)]
fn test_encode_ite_var_condition_bool_prescan_false_branch_is_unsat() {
    let mut encoder = AYEncoder::new_pure();

    let expr = ite(var("flag"), int(1), int(0));
    let term = encoder.encode_pure(&expr).unwrap();
    let flag = *encoder
        .vars_for_test()
        .get("flag")
        .expect("flag should be declared during Bool pre-scan");
    let (zero, flag_false) = {
        let solver = encoder.solver_mut();
        let zero = solver.int_const(0);
        let flag_is_false = solver.bool_const(false);
        let flag_false = solver.eq(flag, flag_is_false);
        (zero, flag_false)
    };
    let gt_term = encoder.solver_mut().gt(term, zero);

    encoder.assert_term(gt_term);
    encoder.assert_term(flag_false);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ite(flag, 1, 0) > 0 AND flag == false should be UNSAT"
    );
}

/// Regression: And(Var("a"), Var("b")) should encode without panic (#544).
#[test]
#[timeout(30000)]
fn test_encode_and_var_operands_bool_prescan() {
    let mut encoder = AYEncoder::new_pure();

    // And(Var("a"), Var("b")) — both must be Bool
    let expr = and(var("a"), var("b"));
    let term = encoder.encode_pure(&expr).unwrap();

    // Assert And(a, b) — should be satisfiable (a = true, b = true)
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "And(a, b) should be SAT (a = true, b = true)"
    );
}

/// Strengthening: And(a, b) should conflict with !a.
#[test]
#[timeout(30000)]
fn test_encode_and_var_operands_bool_prescan_conflict_is_unsat() {
    let mut encoder = AYEncoder::new_pure();

    let expr = and(var("a"), var("b"));
    let term = encoder.encode_pure(&expr).unwrap();
    let a = *encoder
        .vars_for_test()
        .get("a")
        .expect("a should be declared during Bool pre-scan");
    let not_a = encoder.solver_mut().not(a);

    encoder.assert_term(term);
    encoder.assert_term(not_a);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "And(a, b) AND !a should be UNSAT"
    );
}

/// Regression: Eq(Var("x"), Bool(true)) should declare x as Bool (#544).
#[test]
#[timeout(30000)]
fn test_encode_eq_var_bool_propagation() {
    let mut encoder = AYEncoder::new_pure();

    // x == true — x must be Bool
    let expr = eq(var("x"), bool_expr(true));
    let term = encoder.encode_pure(&expr).unwrap();

    // Assert x == true — should be satisfiable
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "x == true should be SAT"
    );
}

/// Strengthening: x == true should conflict with x == false.
#[test]
#[timeout(30000)]
fn test_encode_eq_var_bool_propagation_conflict_is_unsat() {
    let mut encoder = AYEncoder::new_pure();

    let expr = eq(var("x"), bool_expr(true));
    let term = encoder.encode_pure(&expr).unwrap();
    let x = *encoder
        .vars_for_test()
        .get("x")
        .expect("x should be declared during Bool propagation");
    let x_false = {
        let solver = encoder.solver_mut();
        let false_term = solver.bool_const(false);
        solver.eq(x, false_term)
    };

    encoder.assert_term(term);
    encoder.assert_term(x_false);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "x == true AND x == false should be UNSAT"
    );
}
