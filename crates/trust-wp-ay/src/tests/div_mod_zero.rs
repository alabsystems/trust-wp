// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Division/modulo zero-divisor safety obligations.
//!
//! After #1629, `assert_nonzero_divisor` collects `divisor != 0` as a proof
//! obligation (not a solver assumption). The verification layer drains these
//! obligations in `encode_and_assert_negated_postconditions` and conjoins
//! them with postconditions, so an unconstrained divisor causes verification
//! failure (SAT = counterexample with divisor == 0).

use ntest::timeout;

use super::{super::*, helpers::*};

/// At the encoding level (no postcondition negation), division obligations are
/// collected but NOT asserted as solver assumptions. Setting y=0 is therefore
/// satisfiable because no constraint blocks it. The obligation is checked
/// later by the verification layer. (#1629)
#[test]
#[timeout(30000)]
fn test_div_obligation_collected_not_assumed() {
    let mut encoder = AYEncoder::new();
    let expr = div(var("x"), var("y"));
    let _term = encoder
        .encode_pure(&expr)
        .expect("x/y should encode without error");

    // Obligation was collected during encoding
    assert_eq!(
        encoder.division_obligations_for_test().len(),
        1,
        "div(x, y) should collect exactly one division obligation"
    );

    // y=0 is satisfiable because the obligation is NOT a solver assumption (#1629)
    let y = *encoder
        .vars_for_test()
        .get("y")
        .expect("y must be declared after encoding div(x,y)");
    let zero = encoder.solver.int_const(0);
    let y_eq_zero = encoder.solver.eq(y, zero);
    encoder.assert_term(y_eq_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "y=0 must be satisfiable at encoding level — obligation is deferred to verification"
    );
}

/// Same as div: modulo obligations are collected, not assumed. (#1629)
#[test]
#[timeout(30000)]
fn test_mod_obligation_collected_not_assumed() {
    let mut encoder = AYEncoder::new();
    let expr = mod_expr(var("x"), var("y"));
    let _term = encoder
        .encode_pure(&expr)
        .expect("x%y should encode without error");

    assert_eq!(
        encoder.division_obligations_for_test().len(),
        1,
        "mod(x, y) should collect exactly one division obligation"
    );

    let y = *encoder
        .vars_for_test()
        .get("y")
        .expect("y must be declared after encoding mod(x,y)");
    let zero = encoder.solver.int_const(0);
    let y_eq_zero = encoder.solver.eq(y, zero);
    encoder.assert_term(y_eq_zero);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "y=0 must be satisfiable at encoding level — obligation is deferred to verification"
    );
}

/// Divisor!=0 is now a proof obligation, not an assumption. (#1629)
///
/// Encoding `x / y` with unconstrained y no longer assumes y!=0 in the solver.
/// The verification layer (encode_and_assert_negated_postconditions) includes
/// the obligation in the negated conjunction so verification fails when the
/// user hasn't proven the divisor is nonzero.
#[test]
#[timeout(30000)]
fn test_nonzero_divisor_is_obligation_not_assumption() {
    let mut encoder = AYEncoder::new();
    let expr = div(var("x"), var("y"));
    let _term = encoder
        .encode_pure(&expr)
        .expect("x/y should encode without error");

    // Without any user precondition, the solver does NOT know y != 0.
    // The obligation is collected, not assumed. (#1629)
    let y = *encoder
        .vars_for_test()
        .get("y")
        .expect("y must be declared after encoding div(x,y)");
    let zero = encoder.solver.int_const(0);
    let y_eq_zero = encoder.solver.eq(y, zero);
    encoder.assert_term(y_eq_zero);

    // Fixed: Sat because divisor!=0 is an obligation, not an assumption.
    // The verification layer checks this obligation separately.
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "divisor!=0 is now an obligation — y=0 must be satisfiable at encoding level"
    );
}

/// End-to-end: unconstrained divisor prevents verification. (#1629)
///
/// Models a function that divides by an unconstrained variable with a
/// trivial postcondition. Without `y != 0` precondition, the division
/// obligation is unproven. The verifier must NOT return Verified — it
/// must return Failed with a counterexample where y=0.
#[test]
#[timeout(30000)]
fn test_verify_div_unconstrained_divisor_not_verified() {
    let ensures = [ge(var("result"), int(0))];
    let body = div(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "division by unconstrained y must fail with a counterexample, got: {result:?}"
    );
}

/// End-to-end: precondition y != 0 makes division verify. (#1629)
///
/// A function `fn f(x: i32, y: i32) -> i32 { x / y }` with precondition
/// `y != 0` and postcondition `result == x / y` should verify because the
/// precondition satisfies the division obligation.
#[test]
#[timeout(30000)]
fn test_verify_div_with_nonzero_precondition_succeeds() {
    let requires = [ne(var("y"), int(0))];
    let ensures = [eq(var("result"), div(var("x"), var("y")))];
    let body = div(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "division with y != 0 precondition must verify, got: {result:?}"
    );
}

/// End-to-end: modulo with unconstrained divisor prevents verification. (#1629)
///
/// Same pattern as division: the verifier must NOT return Verified when
/// the modulo divisor is unconstrained (no `y != 0` precondition).
#[test]
#[timeout(30000)]
fn test_verify_mod_unconstrained_divisor_not_verified() {
    let ensures = [ge(var("result"), int(0))];
    let body = mod_expr(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "modulo by unconstrained y must fail with a counterexample, got: {result:?}"
    );
}

/// End-to-end: modulo with y != 0 precondition verifies. (#1629)
#[test]
#[timeout(30000)]
fn test_verify_mod_with_nonzero_precondition_succeeds() {
    let requires = [ne(var("y"), int(0))];
    let ensures = [eq(var("result"), mod_expr(var("x"), var("y")))];
    let body = mod_expr(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "modulo with y != 0 precondition must verify, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_binop_div_zero_divisor_guarded_on_dead_branch() {
    let mut encoder = AYEncoder::new();
    let expr = ite(bool_expr(false), div(int(10), var("y")), int(7));
    let term = encoder
        .encode_pure(&expr)
        .expect("ite(false, 10/y, 7) should encode without error");

    // The division is under an unreachable branch, so y == 0 is still SAT.
    let y = *encoder
        .vars_for_test()
        .get("y")
        .expect("y must be declared in dead-branch div encoding");
    let zero = encoder.solver.int_const(0);
    let seven = encoder.solver.int_const(7);
    let y_eq_zero = encoder.solver.eq(y, zero);
    let term_eq_seven = encoder.solver.eq(term, seven);
    encoder.assert_term(y_eq_zero);
    encoder.assert_term(term_eq_seven);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "divisor!=0 obligation must be path-guarded inside dead branches, got: {result:?}"
    );
}

/// Models `ghost_function(x: Int, y: Int, z: Int) -> Int { x + y % z }`
/// with postcondition `result == x + y % z`. Without `total_int_arithmetic`,
/// the modulo obligation `z != 0` prevents verification. With the flag set,
/// the obligation is suppressed (SMT-LIB mod is total). (#1756)
#[test]
#[timeout(30000)]
fn test_ghost_function_mod_with_total_int_arithmetic_verifies() {
    let ensures = [eq(
        var("result"),
        add(var("x"), mod_expr(var("y"), var("z"))),
    )];
    let body = add(var("x"), mod_expr(var("y"), var("z")));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&body))
            .total_int_arithmetic(true),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "ghost function with total_int_arithmetic should verify, got: {result:?}"
    );
}

/// Same scenario as above but WITHOUT total_int_arithmetic. The modulo
/// obligation `z != 0` makes verification fail (correct for machine ints).
#[test]
#[timeout(30000)]
fn test_ghost_function_mod_without_total_int_arithmetic_not_verified() {
    let ensures = [eq(
        var("result"),
        add(var("x"), mod_expr(var("y"), var("z"))),
    )];
    let body = add(var("x"), mod_expr(var("y"), var("z")));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "mod by unconstrained z without total_int_arithmetic must fail with a counterexample, got: {result:?}"
    );
}

/// total_int_arithmetic suppresses div obligations too. (#1756)
#[test]
#[timeout(30000)]
fn test_div_with_total_int_arithmetic_verifies() {
    let ensures = [eq(var("result"), div(var("x"), var("y")))];
    let body = div(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&body))
            .total_int_arithmetic(true),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "div with total_int_arithmetic should verify, got: {result:?}"
    );
}

/// Encoder-level: total_int_arithmetic suppresses obligation collection. (#1756)
#[test]
#[timeout(30000)]
fn test_total_int_arithmetic_no_obligations_collected() {
    let mut encoder = AYEncoder::new();
    encoder.set_total_int_arithmetic(true);
    let expr = mod_expr(var("x"), var("y"));
    let _term = encoder
        .encode_pure(&expr)
        .expect("x%y should encode without error in total mode");

    assert_eq!(
        encoder.division_obligations_for_test().len(),
        0,
        "total_int_arithmetic should suppress obligation collection"
    );
}

/// Mut-borrow path: division with total_int_arithmetic suppresses obligations. (#1800)
///
/// Models `fn halve(v: &mut Int) { *v = *v / 2; }` with postcondition
/// `^v == *v / 2`. Without total_int_arithmetic the obligation `2 != 0`
/// is generated (harmless here, but the mechanism should match the function path).
#[test]
#[timeout(30000)]
fn test_mut_borrow_div_with_total_int_arithmetic_verifies() {
    use std::collections::HashMap;

    // ^v (final) == *v (current) / 2
    let ensures = [eq(var("v_final"), div(var("v_current"), int(2)))];
    // body: v_final = v_current / 2
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), div(var("v_current"), int(2)));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).total_int_arithmetic(true),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "mut-borrow with total_int_arithmetic should verify, got: {result:?}"
    );
}

/// Mut-borrow path WITHOUT total_int_arithmetic: unconstrained divisor fails. (#1800)
///
/// Models `fn div_by_y(v: &mut Int, y: Int) { *v = *v / y; }` with no
/// precondition on `y`. The division obligation `y != 0` should cause
/// verification failure (correct for non-ghost contexts).
#[test]
#[timeout(30000)]
fn test_mut_borrow_div_without_total_int_arithmetic_fails() {
    use std::collections::HashMap;

    let ensures = [eq(var("v_final"), div(var("v_current"), var("y")))];
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), div(var("v_current"), var("y")));

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values));
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "mut-borrow div by unconstrained y without total_int_arithmetic must fail with a counterexample, got: {result:?}"
    );
}
