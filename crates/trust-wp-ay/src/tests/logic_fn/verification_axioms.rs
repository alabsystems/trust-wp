// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

// =========================================================================
// Logic Function Verification Tests (Issue #234)
//
// ay#1926 was fixed - quantifier instantiation now works correctly.
// Use AUFLIA here to exercise the interface term propagation path (#1926).
// =========================================================================

#[test]
#[timeout(30000)]
fn test_ay_quantifier_instantiation_direct() {
    // Direct test of ay's quantifier instantiation
    // This bypasses trust-wp's encoding to verify ay works correctly
    //
    // We want to verify:
    // 1. Declare f: Int -> Int (uninterpreted function)
    // 2. Assert axiom: forall x. f(x) = x * 2
    // 3. Declare constant c: Int
    // 4. Assert c = 5
    // 5. Assert f(c) != 10
    // 6. Check SAT - should be UNSAT (axiom instantiated at c gives f(5) = 10)
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::Auflia).unwrap();

    // Declare uninterpreted function f: Int -> Int
    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("f declaration should succeed");

    // Create bound variable for axiom
    let qvar = solver.fresh_var("qx", Sort::Int);

    // Build axiom body: f(qx) = qx * 2
    let f_qx = solver
        .try_apply(&f, &[qvar])
        .expect("f(qx) application should succeed");
    let two = solver.int_const(2);
    let qx_times_2 = solver.mul(qvar, two);
    let axiom_body = solver.eq(f_qx, qx_times_2);

    // Create axiom: forall qx. f(qx) = qx * 2
    let axiom = solver.forall(&[qvar], axiom_body);
    solver.assert_term(axiom);

    // Declare constant c
    let c = solver.declare_const("c", Sort::Int);

    // Assert c = 5
    let five = solver.int_const(5);
    let c_eq_5 = solver.eq(c, five);
    solver.assert_term(c_eq_5);

    // Assert f(c) != 10
    let f_c = solver
        .try_apply(&f, &[c])
        .expect("f(c) application should succeed");
    let ten = solver.int_const(10);
    let f_c_eq_10 = solver.eq(f_c, ten);
    let f_c_ne_10 = solver.not(f_c_eq_10);
    solver.assert_term(f_c_ne_10);

    // With axiom: f(c) = c * 2, with c = 5: f(5) = 10
    // But we asserted f(c) != 10, contradiction -> should be UNSAT
    // ay#1926 was fixed - quantifier instantiation now works correctly.
    let result = solver.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Expected UNSAT (f(5)=10, asserted f(5)!=10 is contradiction), got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_ay_gt_with_uf_axiom_unsound() {
    // Regression test for ay#1975 soundness bug at the solver level (dup ay#1974).
    //
    // The original quantified UF encoding:
    //   forall x. add_one(x) = x + 1
    // is satisfiable here, but this ay pin deliberately fails closed to Unknown
    // for SAT results involving universal quantifiers that are not fully
    // certified. Use define-fun so add_one(y) expands to y + 1 and this remains
    // a decidable quantifier-free arithmetic regression.
    //
    // This formula is SATISFIABLE:
    //   - add_one(y) = y + 1 (from inline definition)
    //   - result = y + 1 (asserted)
    //   - NOT((y+1) > (y+1)) = NOT(false) = true
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    // Define add_one : Int -> Int as add_one(n) = n + 1.
    let add_one_decl = solver
        .try_define_fun("add_one", &[("n", Sort::Int)], Sort::Int, |s, params| {
            let one = s.int_const(1);
            s.try_add(params[0], one)
        })
        .expect("add_one declaration should succeed");

    // Declare global variables
    let y = solver.declare_const("y", Sort::Int);
    let result = solver.declare_const("result", Sort::Int);

    // Constraint 1: y >= 0
    let zero = solver.int_const(0);
    let y_ge_0 = solver.ge(y, zero);
    solver.assert_term(y_ge_0);

    // Constraint 2: result = y + 1
    let one_const = solver.int_const(1);
    let y_plus_one = solver.add(y, one_const);
    let result_eq_body = solver.eq(result, y_plus_one);
    solver.assert_term(result_eq_body);

    // Constraint 3: NOT(result > add_one(y))
    let add_one_y = solver
        .try_apply(&add_one_decl, &[y])
        .expect("add_one(y) application should succeed");
    let result_gt_add_one = solver.gt(result, add_one_y);
    let neg_post = solver.not(result_gt_add_one);
    solver.assert_term(neg_post);

    let result_check = solver.check_sat().into_inner();

    // Fixed in ay#1975 (commit 443907a1): LIA now correctly handles UF Int terms
    // Formula is satisfiable: NOT((y+1) > (y+1)) = NOT(false) = true
    assert!(
        matches!(result_check, SolveResult::Sat),
        "Formula is satisfiable: NOT((y+1) > (y+1)) is true. Got: {result_check:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_logic_fn_axiom_enables_verification() {
    // Test that logic function axioms actually enable verification
    //
    // Logic function: double(x) = x * 2
    // Precondition: x == 5
    // Postcondition: result == double(x)
    // Body: result = 10
    //
    // Without axioms: FAILS (result == double(x) is unconstrained)
    // With axioms: VERIFIED (axiom says double(5) = 5*2 = 10)
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        mul(var("x"), int(2)),
    )
    .with_mode(LogicMode::Open);

    // requires: x == 5
    let requires = vec![eq(var("x"), int(5))];

    // ensures: result == double(x)
    let ensures = vec![eq(var("result"), logic_fn_call("double", vec![var("x")]))];

    // body: result = 10 (which equals double(5) = 5*2)
    let return_expr = int(10);

    // Verify WITH logic functions - should pass now that ay#1926 is fixed
    let result_with_axiom = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );

    // ay#1926 was fixed - axiom instantiation now works correctly
    assert!(
        matches!(result_with_axiom, Ok(VerificationResult::Verified(_))),
        "Expected Verified (double(5)=10 via axiom), got: {result_with_axiom:?}"
    );

    // Verify WITHOUT logic functions - should not verify (underconstrained).
    let result_without_axiom = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(result_without_axiom, Ok(VerificationResult::Failed(_))),
        "Without logic function axiom, double(x) is unconstrained UF — solver \
         should fail: got {result_without_axiom:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_logic_fn_axiom_symbolic() {
    // Test that logic function axioms work with SYMBOLIC x (no precondition)
    // This mirrors the fixture test case.
    //
    // Logic function: add_one(x) = x + 1
    // Precondition: NONE (x is symbolic)
    // Postcondition: result == add_one(x)
    // Body: result = x + 1
    //
    // The axiom should allow proving: (x + 1) == add_one(x) for all x
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new(
        "add_one".to_string(),
        "test::add_one".to_string(),
        vec!["x".to_string()],
        // add_one(x) = x + 1
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // NO preconditions - x is symbolic
    let requires: Vec<PureExpr> = vec![];

    // ensures: result == add_one(x)
    let ensures = vec![eq(var("result"), logic_fn_call("add_one", vec![var("x")]))];

    // body: result = x + 1
    let return_expr = add(var("x"), int(1));

    // Verify WITH logic functions - should pass
    // NOTE: Bug #259 (blocked on ay#1939) - registering multiple logic
    // functions breaks quantifier instantiation. Only register the needed function.
    let result_with_axiom = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );

    assert!(
        matches!(result_with_axiom, Ok(VerificationResult::Verified(_))),
        "Expected Verified (x+1 == add_one(x) via axiom), got: {result_with_axiom:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_logic_fn_axiom_symbolic_view_param_uses_caller_argument() {
    // Regression for #1635: after preserving turbofish const args, the
    // call-site argument reaches the logic-function application, but the axiom
    // body must also evaluate `View(param)` against that same caller argument.
    // This mirrors the failing shape from `lang/const.rs`: formal `p`, caller `m`.
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new(
        "add_one_view".to_string(),
        "test::add_one_view".to_string(),
        vec!["p".to_string()],
        add(view(var("p")), int(1)),
    )
    .with_mode(LogicMode::Open);

    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(
        var("result"),
        logic_fn_call("add_one_view", vec![var("m")]),
    )];
    let return_expr = add(var("m"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Expected Verified when the logic-function body reuses caller arg m for p@ + 1, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_logic_fn_axiom_respects_requires_guard() {
    // Test that logic function axioms are guarded by preconditions.
    //
    // Logic function: pos(x) = x, requires x > 0
    // Function precondition: x == -1
    // Postcondition: result == pos(x)
    // Body: result = -1
    //
    // With guarded axiom: should FAIL (axiom doesn't apply for x == -1)
    // Without guard: should VERIFY (axiom forces pos(-1) = -1)
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let guarded_logic_fn = LogicFnDef::new_with_requires(
        "pos".to_string(),
        "test::pos".to_string(),
        vec!["x".to_string()],
        vec![gt(var("x"), int(0))],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    let requires = vec![eq(var("x"), int(-1))];

    let ensures = vec![eq(var("result"), logic_fn_call("pos", vec![var("x")]))];

    let return_expr = int(-1);

    let result_with_guard = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&guarded_logic_fn))),
    );

    assert!(
        matches!(result_with_guard, Ok(VerificationResult::Failed(_))),
        "Expected Failed when logic function precondition is violated, got: {result_with_guard:?}"
    );

    let unguarded_logic_fn = LogicFnDef::new(
        "pos".to_string(),
        "test::pos".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    let result_without_guard = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&unguarded_logic_fn))),
    );

    assert!(
        matches!(result_without_guard, Ok(VerificationResult::Verified(_))),
        "Expected Verified when axiom is unguarded, got: {result_without_guard:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_logic_fn_impossible_postcondition_ay_bug() {
    // Regression test for ay soundness bug (trust-wp #307, ay #1975 / dup #1974)
    //
    // Logic function: add_one(x) = x + 1
    // Precondition: x >= 0
    // Postcondition: result > add_one(x)  <-- IMPOSSIBLE: result is x+1, add_one(x) is x+1
    // Body: result = x + 1
    //
    // This should FAIL verification because (x+1) > (x+1) is always false.
    //
    // KNOWN BUG: ay#1975 (dup ay#1974) - E-matching fails to propagate equality for UF+LIA comparison.
    // When ay#1975 is fixed, change the assertion below from Verified to Failed.
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new(
        "add_one".to_string(),
        "test::add_one".to_string(),
        vec!["x".to_string()],
        // add_one(x) = x + 1
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // requires: x >= 0
    let requires = vec![ge(var("x"), int(0))];

    // ensures: result > add_one(x)
    // This is IMPOSSIBLE since body returns x+1 and add_one(x) = x+1
    let ensures = vec![gt(var("result"), logic_fn_call("add_one", vec![var("x")]))];

    // body: result = x + 1
    let return_expr = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );

    // Fixed in ay#1975 (commit 443907a1): LIA correctly handles UF Int terms.
    // Postcondition `result > add_one(x)` is impossible: (x+1) > (x+1) is false.
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "Postcondition `result > add_one(x)` is impossible and should fail. Got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_logic_fn_requires_binds_param_guard() {
    // Test that logic function requires are encoded with bound parameters.
    //
    // Logic function: pos(x) = x, requires x > 0
    // Function precondition: x > 0
    // Postcondition: result == pos(x)
    // Body: result = x
    //
    // With correctly bound guard: should VERIFY.
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new_with_requires(
        "pos".to_string(),
        "test::pos".to_string(),
        vec!["x".to_string()],
        vec![gt(var("x"), int(0))],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    let requires = vec![gt(var("x"), int(0))];

    let ensures = vec![eq(var("result"), logic_fn_call("pos", vec![var("x")]))];

    let return_expr = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Expected Verified when guard uses bound parameter, got: {result:?}"
    );
}
