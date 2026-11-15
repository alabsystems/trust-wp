// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
/// Regression test for #1179: short-circuit && encoding consistency.
///
/// The MIR desugaring of `a.func1(b) && b.func2(a) && a.func3(b)` produces
/// `Ite(_call_3, Ite(_call_6, _call_0, false), false)`. With postcondition
/// `ensures(result == false)`, verification should produce a CONSISTENT
/// counterexample where `result == true` (because the body forces
/// `result = Ite(true, Ite(true, true, false), false) = true`).
///
/// The defect this pins: a counterexample with `result = false` and all calls
/// true — an inconsistent model, possible only when `result = body` is not
/// constraining the solver.
#[test]
#[timeout(30000)]
fn test_short_circuit_and_body_constrains_result() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // ensures(result == false)
    let ensures = vec![eq(var("result"), bool_expr(false))];
    // body: Ite(_call_3, Ite(_call_6, _call_0, false), false)
    // This is the MIR desugaring of func1() && func2() && func3()
    let body = ite(
        var("_call_3"),
        ite(var("_call_6"), var("_call_0"), bool_expr(false)),
        bool_expr(false),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .unwrap_or_else(|err| panic!("Verification should not panic: {err:?}"));
    // The postcondition `result == false` is NOT always true (calls can all return true),
    // so verification should fail with a counterexample.
    let VerificationResult::Failed(cex) = &result else {
        panic!("Expected Failed, got: {result:?}");
    };

    // The counterexample must be CONSISTENT: if the body says
    // result = Ite(true, Ite(true, true, false), false), then result must be true.
    // Check that the model has result = true (not result = false).
    let result_bool = cex.bool_assignments().find(|(name, _)| *name == "result");
    assert!(
        result_bool.is_some(),
        "Counterexample must include 'result' bool binding: {cex:?}"
    );
    assert!(
        result_bool.unwrap().1,
        "result must be true in counterexample (body forces result = Ite(true, ...) = true). \
         If result=false, the body constraint is not constraining 'result'. \
         Full counterexample: {cex:?}"
    );
}

/// Regression test for #1179: short-circuit || encoding consistency.
///
/// The MIR desugaring of `a.func1(b) || b.func2(a)` produces
/// `Ite(_call_1, true, _call_0)`. With postcondition `ensures(result == true)`,
/// verification should produce a CONSISTENT counterexample where `result == false`.
#[test]
#[timeout(30000)]
fn test_short_circuit_or_body_constrains_result() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // ensures(result == true)
    let ensures = vec![eq(var("result"), bool_expr(true))];
    // body: Ite(_call_1, true, _call_0)
    // This is the MIR desugaring of func1() || func2()
    let body = ite(var("_call_1"), bool_expr(true), var("_call_0"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .unwrap_or_else(|err| panic!("Verification should not panic: {err:?}"));
    // The postcondition `result == true` is NOT always true (calls can all return false),
    // so verification should fail with a counterexample.
    let VerificationResult::Failed(cex) = &result else {
        panic!("Expected Failed, got: {result:?}");
    };

    // The counterexample must be CONSISTENT: if both calls return false,
    // the body Ite(_call_1=false, true, _call_0=false) = false.
    let result_bool = cex.bool_assignments().find(|(name, _)| *name == "result");
    assert!(
        result_bool.is_some(),
        "Counterexample must include 'result' bool binding: {cex:?}"
    );
    assert!(
        !result_bool.unwrap().1,
        "result must be false in counterexample (both calls false => body = false). \
         Full counterexample: {cex:?}"
    );
}

/// Most basic test: just assert(result), check result = true in model
#[test]
#[timeout(30000)]
fn test_most_basic_bool_model() {
    let mut encoder = AYEncoder::new_pure();

    let result = encoder
        .solver
        .declare_const("result", ay_dpll::api::Sort::Bool);
    encoder.solver.assert_term(result);

    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Sat),
        "assert(result) with Bool result should be SAT"
    );

    let model = encoder.get_model();
    let m = model.unwrap();
    let (_, val) = m
        .iter_bools()
        .find(|(name, _)| *name == "result")
        .expect("result must be in model");
    assert!(val, "result must be true when assert(result)");
}

/// Test: explicit iff encoding `(result => c) AND (c => result)` is
/// satisfiable with `result != false`.
///
/// This keeps a direct sanity check for manual biconditional encoding, even
/// though Bool equality goes through solver `eq` directly.
#[test]
#[timeout(30000)]
fn test_bool_iff_encoding_is_consistent() {
    let mut encoder = AYEncoder::new_pure();

    let c = encoder.solver.declare_const("c", ay_dpll::api::Sort::Bool);
    let result = encoder
        .solver
        .declare_const("result", ay_dpll::api::Sort::Bool);

    // Assert: result <=> c  using (result => c) AND (c => result)
    let r_implies_c = encoder.solver.implies(result, c);
    let c_implies_r = encoder.solver.implies(c, result);
    let iff = encoder.solver.and(r_implies_c, c_implies_r);
    encoder.solver.assert_term(iff);

    // Assert: NOT(result = false)
    let f = encoder.solver.bool_const(false);
    let result_eq_false = encoder.solver.eq(result, f);
    let neg = encoder.solver.not(result_eq_false);
    encoder.solver.assert_term(neg);

    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Sat),
        "result <=> c with NOT(result = false) should be SAT"
    );

    let model = encoder.get_model();
    let m = model.unwrap();
    let (_, val) = m
        .iter_bools()
        .find(|(name, _)| *name == "result")
        .expect("result must be in model for iff encoding");
    assert!(val, "result must be true with iff encoding");
}

/// Verify that a failing postcondition produces a counterexample with
/// meaningful variable bindings, not just an empty or garbage model.
///
/// Tests #552 item 5: counterexample quality was never inspected.
///
/// Contract: requires(x > 0), ensures(result > 10), body = x + 1.
/// For x=1, result=2 which violates result > 10.
// KNOWN-CLASS LOAD FLAKE (#133) — root cause named, budget deliberately
// UNCHANGED.
//
// This test's own work takes about 0.01s and passes solo. Its in-suite failure
// is not its own solve, it is time queued behind `encoder::test_solver_limiter`,
// the crate's global 8-permit cap on concurrent solver instances — and ntest's
// `#[timeout]` measures wall-clock, queueing included.
//
// The budget is NOT the lever, and this was MEASURED, not assumed: at 120s the
// test waits the full 120s of a 127s suite and never acquires a permit, while
// the added 90s of occupancy pushes a second test
// (`body_break_basic_loop_verifies`, also green solo) over its own budget.
//
// The real defect is that `acquire_solver_permit` is a BARGING semaphore
// (`Condvar::notify_one` + a `while count >= max` re-check): an arriving thread
// can take the permit before a woken waiter re-acquires the mutex, so with
// thousands of short acquisitions a waiter can starve for a whole run. The
// obvious fix — FIFO ticketing — is NOT applied here because it is not
// obviously safe: a test that holds one permit while constructing a second
// encoder would, under strict FIFO with max == test-threads == 8, deadlock
// where barging merely delays. Fixing it properly needs a permit budget per
// test thread (or a re-entrant permit), which is its own change with its own
// gate, not a timeout edit.
#[test]
#[timeout(30000)]
fn test_counterexample_contains_meaningful_bindings() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let requires = vec![gt(var("x"), int(0))];
    let ensures = vec![gt(var("result"), int(10))];
    // body: result = x + 1
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    );
    let cex = match result {
        Ok(VerificationResult::Failed(cex)) => cex,
        other => panic!("Expected Failed with counterexample, got: {other:?}"),
    };

    // The counterexample should contain at least one variable binding.
    assert!(
        cex.int_assignments().next().is_some(),
        "Counterexample should contain integer variable assignments, got empty"
    );

    // The model should include "x" with a concrete positive value.
    let x_val = cex
        .int_assignments()
        .find(|(name, _)| *name == "x")
        .map(|(_, v)| v)
        .expect("Counterexample should contain 'x' variable binding");
    assert!(
        x_val > 0,
        "Counterexample x should satisfy precondition (x > 0), got x = {x_val}"
    );

    // The model must include "result" — verify it violates the postcondition.
    let result_val = cex
        .int_assignments()
        .find(|(name, _)| *name == "result")
        .map(|(_, v)| v)
        .expect("Counterexample should contain 'result' variable binding");
    assert!(
        result_val <= 10,
        "Counterexample result should violate ensures (result > 10), got result = {result_val}"
    );
    assert_eq!(
        result_val,
        x_val + 1,
        "Counterexample result should equal x + 1"
    );
}

/// Diagnostic: test raw ay solver with array select to isolate Unknown-on-SAT
/// root cause. Part of #1603 failure triage.
#[test]
#[timeout(30000)]
fn test_diagnostic_raw_array_select_sat() {
    use ay_dpll::api::{Logic, Solver, Sort};
    // Test 1: Raw solver (no AYEncoder), QF_AUFLIA, array select
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let idx = solver.declare_const("idx", Sort::Int);
    let sel = solver
        .try_select(arr, idx)
        .expect("arr[idx] select should succeed");
    let val42 = solver.int_const(42);
    let eq = solver.eq(sel, val42);
    solver.assert_term(eq);
    let r1 = solver.check_sat().into_inner();
    eprintln!("[diag] raw QF_AUFLIA array select(arr, idx) == 42: {r1:?}");

    // Test 2: Raw solver, QF_AUFLIA, Bool array select
    let mut solver2 = Solver::try_new(Logic::QfAuflia).unwrap();
    let dom = solver2.declare_const("dom", Sort::array(Sort::Int, Sort::Bool));
    let loc = solver2.declare_const("loc", Sort::Int);
    let in_dom = solver2
        .try_select(dom, loc)
        .expect("dom[loc] select should succeed");
    solver2.assert_term(in_dom); // assert select(dom, loc) is true
    let r2 = solver2.check_sat().into_inner();
    eprintln!("[diag] raw QF_AUFLIA Bool-array select(dom, loc): {r2:?}");

    // Test 3: Combined — mimics PointsTo encoding
    let mut solver3 = Solver::try_new(Logic::QfAuflia).unwrap();
    let heap = solver3.declare_const("heap", Sort::array(Sort::Int, Sort::Int));
    let domain = solver3.declare_const("domain", Sort::array(Sort::Int, Sort::Bool));
    let perms = solver3.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
    let loc3 = solver3.declare_const("loc", Sort::Int);
    let in_domain = solver3
        .try_select(domain, loc3)
        .expect("domain[loc] select should succeed");
    let heap_val = solver3
        .try_select(heap, loc3)
        .expect("heap[loc] select should succeed");
    let perm_val = solver3
        .try_select(perms, loc3)
        .expect("perms[loc] select should succeed");
    let val_42 = solver3.int_const(42);
    let perm_2520 = solver3.int_const(2520);
    let heap_eq = solver3.eq(heap_val, val_42);
    let perm_ok = solver3.ge(perm_val, perm_2520);
    let c1 = solver3.and(in_domain, perm_ok);
    let c2 = solver3.and(c1, heap_eq);
    solver3.assert_term(c2);
    let r3 = solver3.check_sat().into_inner();
    eprintln!("[diag] raw QF_AUFLIA PointsTo-style (domain+perms+heap): {r3:?}");

    // Test 4: Through AYEncoder path
    let mut encoder = AYEncoder::new();
    let formula = points_to("loc", int(42));
    let term = encoder.encode(&formula).unwrap();
    encoder.assert_term(term);
    let r4 = encoder.check_sat();
    eprintln!("[diag] AYEncoder PointsTo(loc, 42): {r4:?}");

    // Test 5: Workaround — use Int array for domain, compare select == 1
    let mut solver5 = Solver::try_new(Logic::QfAuflia).unwrap();
    let heap5 = solver5.declare_const("heap", Sort::array(Sort::Int, Sort::Int));
    let domain5 = solver5.declare_const("domain", Sort::array(Sort::Int, Sort::Int));
    let perms5 = solver5.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
    let loc5 = solver5.declare_const("loc", Sort::Int);
    let in_domain5 = solver5
        .try_select(domain5, loc5)
        .expect("domain5[loc5] select should succeed");
    let one = solver5.int_const(1);
    let in_domain_ok = solver5.eq(in_domain5, one); // domain[loc] == 1 instead of Bool
    let heap_val5 = solver5
        .try_select(heap5, loc5)
        .expect("heap5[loc5] select should succeed");
    let perm_val5 = solver5
        .try_select(perms5, loc5)
        .expect("perms5[loc5] select should succeed");
    let val_42_5 = solver5.int_const(42);
    let perm_2520_5 = solver5.int_const(2520);
    let heap_eq5 = solver5.eq(heap_val5, val_42_5);
    let perm_ok5 = solver5.ge(perm_val5, perm_2520_5);
    let c1_5 = solver5.and(in_domain_ok, perm_ok5);
    let c2_5 = solver5.and(c1_5, heap_eq5);
    solver5.assert_term(c2_5);
    let r5 = solver5.check_sat().into_inner();
    eprintln!("[diag] Int-domain workaround PointsTo-style: {r5:?}");

    // At least the raw solver tests should be SAT
    assert!(
        matches!(r1, SolveResult::Sat),
        "Raw array select(arr, idx) == 42 should be SAT, got: {r1:?}"
    );
    assert!(
        matches!(r5, SolveResult::Sat),
        "Int-domain workaround should be SAT, got: {r5:?}"
    );
}
