// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn test_verify_increment() {
    // requires: x > 0
    // ensures: result > x
    // body: x + 1
    let req = gt(var("x"), int(0));
    let ens = gt(var("result"), var("x"));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("increment verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x+1 > x given x > 0 should verify: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_invariant_method_round_trip() {
    // requires: x.invariant()
    // ensures: result.invariant()
    // body: result = x
    let req = method_call(var("x"), "invariant", vec![]);
    let ens = method_call(var("result"), "invariant", vec![]);
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "invariant predicate should transfer across result == x: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_invariant_method_missing_precondition_fails() {
    // ensures: result.invariant()
    // body: result = x
    // Without a precondition, this should fail for an uninterpreted predicate.
    let ens = method_call(var("result"), "invariant", vec![]);
    let body = var("x");

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("missing-precondition verification should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "postcondition invariant(result) requires supporting assumptions: {result:?}"
    );
}

/// Type invariant auto-injection pattern: user contract + invariant precondition (#359).
///
/// Simulates auto-injection for a function like:
///   #[requires(x.value > 0)]
///   #[ensures(result.value > 0)]
///   fn identity(x: NonZero) -> NonZero { x }
///
/// with auto-injected: requires(x.invariant()), ensures(result.invariant())
/// Verifies that explicit user contracts compose with injected invariant clauses.
#[test]
#[timeout(30000)]
fn test_verify_invariant_auto_injection_with_user_contract() {
    // User contract: requires(x > 0), ensures(result > 0)
    let user_req = gt(var("x"), int(0));
    let user_ens = gt(var("result"), int(0));
    // Auto-injected: requires(x.invariant()), ensures(result.invariant())
    let inv_req = method_call(var("x"), "invariant", vec![]);
    let inv_ens = method_call(var("result"), "invariant", vec![]);
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[user_req, inv_req], &[user_ens, inv_ens])
            .return_expr(Some(&body)),
    )
    .expect("invariant auto-injection composition should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "user contract + auto-injected invariant should compose: {result:?}"
    );
}

/// Type invariant auto-injection for `&mut` parameter (#359).
///
/// Simulates auto-injection for `fn foo(x: &mut NonZero)` where the
/// injected precondition uses `(*x).invariant()` (dereferenced receiver).
#[test]
#[timeout(30000)]
fn test_verify_invariant_mut_ref_param_injection() {
    // Auto-injected: requires((*x).invariant())
    let inv_req = method_call(deref(var("x")), "invariant", vec![]);
    // User contract: ensures(result.invariant())
    // body: result = *x (identity through deref)
    let inv_ens = method_call(var("result"), "invariant", vec![]);
    let body = deref(var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[inv_req], &[inv_ens]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "(*x).invariant() should transfer to result.invariant() via result == *x: {result:?}"
    );
}

/// Type invariant injection with mixed primitive and non-primitive params (#359).
///
/// Simulates: fn combine(n: i32, x: Custom) -> Custom
/// Only `x` gets invariant injection (i32 has trivial invariant).
/// If x.invariant() is assumed and result == x, result.invariant() holds.
#[test]
#[timeout(30000)]
fn test_verify_invariant_selective_injection_non_primitive_only() {
    // User contract: requires(n > 0)
    let user_req = gt(var("n"), int(0));
    // Auto-injected only for non-primitive `x`: requires(x.invariant())
    let inv_req = method_call(var("x"), "invariant", vec![]);
    // Auto-injected for return type: ensures(result.invariant())
    let inv_ens = method_call(var("result"), "invariant", vec![]);
    // Body: result = x (ignoring n)
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[user_req, inv_req], &[inv_ens]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "selective invariant injection (non-primitive only) should verify: {result:?}"
    );
}

/// Type invariant body axiom: constructor proves invariant (#359, #645).
///
/// Simulates a NonZero type with invariant `self > 0`.
/// Constructor: requires(n > 0), body: result = n
/// Auto-injected: ensures(result.invariant())
///
/// Without the invariant body axiom, the solver can't prove result.invariant()
/// because it's an uninterpreted predicate. With the axiom
/// `forall x. invariant(x) = (x > 0)`, the solver can use `n > 0` to prove
/// `invariant(n)` which is `n > 0`.
#[test]
#[timeout(30000)]
fn test_verify_invariant_body_axiom_constructor_proof() {
    use ay_dpll::api::Sort;

    // Set up encoder directly to register the invariant body axiom
    let mut encoder = AYEncoder::new();

    // Register: forall self. invariant(self) = (self > 0)
    let invariant_body = gt(var("self"), int(0));
    encoder
        .register_type_invariant("MyType", "self", Sort::Int, &invariant_body)
        .expect("invariant registration should succeed");

    // Encode the verification: requires(n > 0), ensures(result.invariant()), body: result = n
    // 1. Declare variables
    let n = encoder
        .get_or_declare_var("n", Sort::Int)
        .expect("declare n");
    let result = encoder
        .get_or_declare_var("result", Sort::Int)
        .expect("declare result");

    // 2. Assert precondition: n > 0
    let zero = encoder.solver.int_const(0);
    let n_gt_0 = encoder.solver.gt(n, zero);
    encoder.solver.assert_term(n_gt_0);

    // 3. Assert body: result = n
    let result_eq_n = encoder.solver.eq(result, n);
    encoder.solver.assert_term(result_eq_n);

    // 4. Assert negation of postcondition: NOT(result.__trust_wp_invariant_MyType())
    let method_name = trust_wp_core::logic::type_invariant_method_name("MyType");
    let inv_result = encoder
        .encode_pure(&method_call(var("result"), &method_name, vec![]))
        .expect("invariant encoding should succeed");
    let not_inv = encoder.solver.not(inv_result);
    encoder.solver.assert_term(not_inv);

    // Check: should be UNSAT (postcondition holds)
    let solve_result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(solve_result, ay_dpll::api::SolveResult::Unsat(_)),
        "with invariant body axiom, constructor should prove result.invariant(): {solve_result:?}"
    );
}

/// Type invariant body axiom: missing precondition fails (#359, #645).
///
/// Same as above but WITHOUT the requires(n > 0) precondition.
/// The solver should find a counterexample (n = 0 or negative).
#[test]
#[timeout(30000)]
fn test_verify_invariant_body_axiom_missing_precondition_fails() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();

    // Register: forall self. invariant(self) = (self > 0)
    let invariant_body = gt(var("self"), int(0));
    encoder
        .register_type_invariant("MyType", "self", Sort::Int, &invariant_body)
        .expect("invariant registration should succeed");

    // No precondition on n
    let n = encoder
        .get_or_declare_var("n", Sort::Int)
        .expect("declare n");
    let result = encoder
        .get_or_declare_var("result", Sort::Int)
        .expect("declare result");

    // body: result = n
    let result_eq_n = encoder.solver.eq(result, n);
    encoder.solver.assert_term(result_eq_n);

    // NOT(result.__trust_wp_invariant_MyType())
    let method_name = trust_wp_core::logic::type_invariant_method_name("MyType");
    let inv_result = encoder
        .encode_pure(&method_call(var("result"), &method_name, vec![]))
        .expect("invariant encoding should succeed");
    let not_inv = encoder.solver.not(inv_result);
    encoder.solver.assert_term(not_inv);

    // Check: should be SAT (counterexample: n <= 0).
    let solve_result = encoder.solver.check_sat().into_inner();
    assert!(
        matches!(solve_result, ay_dpll::api::SolveResult::Sat),
        "without precondition, invariant proof should produce a SAT counterexample: {solve_result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_function_reg_track_level() {
    // Test that TrackLevel::Reg uses pure encoder (no heap arrays)
    // This verifies #275 Phase 2 implementation
    //
    // Pure function should work with Reg mode since it doesn't use heap.
    use trust_wp_core::TrackLevel;

    let req = gt(var("x"), int(0));
    let ens = gt(var("result"), int(0));
    let body = add(var("x"), int(1));

    // Explicit Reg mode - should use new_pure() encoder
    let result = verify_function_with_modes(
        VerificationRequest::new(std::slice::from_ref(&req), std::slice::from_ref(&ens))
            .return_expr(Some(&body))
            .track(Some(TrackLevel::Reg)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Reg track level should verify pure function: {result:?}"
    );

    // Auto mode - should default to Reg behavior for pure functions
    let result_auto = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .track(Some(TrackLevel::Auto)),
    );
    assert!(
        matches!(result_auto, Ok(VerificationResult::Verified(_))),
        "Auto track level should verify pure function: {result_auto:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_failing_contract() {
    // requires: x > 0
    // ensures: result < x (wrong - should fail)
    // body: x + 1
    let req = gt(var("x"), int(0));
    let ens = lt(var("result"), var("x"));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "x > 0 with ensures result < x but body = x + 1 should fail, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_decrement() {
    // Verify mutable borrow decrement via verify_mut_borrow_function (#542):
    // #[requires(*v > i32::MIN)]
    // #[ensures(^v == old(*v) - 1)]
    // fn decrement(v: &mut i32) { *v -= 1; }
    //
    // Exercises the full encoding pipeline (PureExpr → SMT terms),
    // including Deref→current, Final→final naming and Sub encoding.
    let req = gt(deref(var("v")), int(i64::from(i32::MIN)));
    let ens = eq(final_expr(var("v")), sub(old(deref(var("v"))), int(1)));

    // body: *v - 1
    let body_expr = sub(deref(var("v")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "decrement should verify: got {result:?}"
    );
}

// ============================================================================
// Coverage gap tests: TrackLevel::Ptr, TrackLevel::Mem
// ============================================================================

/// Test `verify_function` with `TrackLevel::Ptr` (heap-aware encoder).
///
/// The Ptr track level selects `AYEncoder::new()` (heap-aware with arrays)
/// instead of `AYEncoder::new_pure()`. This path at verify.rs:339 was
/// previously untested.
///
/// Uses a pure function to verify the heap-aware encoder handles
/// non-heap expressions correctly (it should be a superset of the pure encoder).
#[test]
#[timeout(30000)]
fn test_verify_function_ptr_track_level() {
    use trust_wp_core::TrackLevel;

    let req = gt(var("x"), int(0));
    let ens = gt(var("result"), var("x"));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .track(Some(TrackLevel::Ptr)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Ptr track level should verify pure function: {result:?}"
    );
}

/// Test `verify_function` with `TrackLevel::Mem` (full memory model encoder).
///
/// The Mem track level also selects `AYEncoder::new()`. This path at
/// verify.rs:339 was previously untested.
#[test]
#[timeout(30000)]
fn test_verify_function_mem_track_level() {
    use trust_wp_core::TrackLevel;

    let req = ge(var("x"), int(0));
    let ens = ge(var("result"), int(0));
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .track(Some(TrackLevel::Mem)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Mem track level should verify pure function: {result:?}"
    );
}

/// Test `verify_function` with failing contract under Ptr track level.
///
/// Ensures the heap-aware encoder correctly detects counterexamples.
#[test]
#[timeout(30000)]
fn test_verify_function_ptr_track_level_failing() {
    use trust_wp_core::TrackLevel;

    let req = gt(var("x"), int(0));
    // Wrong: result < x (should be result > x for body x + 1)
    let ens = lt(var("result"), var("x"));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .track(Some(TrackLevel::Ptr)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "Ptr track level should detect wrong postcondition: {result:?}"
    );
}
