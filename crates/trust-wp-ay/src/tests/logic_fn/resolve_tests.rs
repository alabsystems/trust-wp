// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ntest::timeout;

use super::*;

// =============================================================================
// Resolve predicate encoding tests (Phase 4, Part of #358)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_encode_resolve_simple() {
    // resolve(x) encodes as x_current == x_final (Bool-sorted equality).
    // Without constraining x_current != x_final, this should be SAT
    // because the solver can unify both fresh variables.
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("resolve", vec![var("x")]);

    let term = encoder
        .encode_pure(&expr)
        .expect("resolve(x) should encode without error");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        ay_dpll::api::SolveResult::Sat,
        "resolve(x) should be satisfiable when x_current and x_final are unconstrained"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_encodes_as_boolean() {
    // resolve(x) should encode as a Bool-sorted term (equality).
    // We test this indirectly: resolve(x) && true should encode without
    // sort mismatch errors, which would occur if resolve returned Int.
    // Semantic: resolve(x) && true is Sat (same as resolve(x)). Part of #1990.
    let mut encoder = AYEncoder::new();

    let resolve_call = logic_fn_call("resolve", vec![var("x")]);

    // resolve(x) && true — this requires resolve to be Bool-sorted
    let conj = and(resolve_call, bool_expr(true));

    let term = encoder
        .encode_pure(&conj)
        .expect("resolve(x) && true should encode (Bool-sorted)");

    // Semantic: resolve(x) && true is satisfiable (same as resolve(x) alone)
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "resolve(x) && true is satisfiable (unconstrained x) (#1990)"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_mut_borrow_verified() {
    // Verify: fn f(v: &mut i32) { *v += 1; }
    // with: requires(*v > i32::MIN), ensures(^v == *v + 1)
    //
    // The postcondition is compatible with resolve: after the borrow ends,
    // v_current (entry value + 1) == v_final. This does NOT directly use
    // resolve() in the contract, but tests the same encoding path.
    let req = gt(deref(var("v")), int(i64::from(i32::MIN)));

    let ens = eq(final_expr(var("v")), add(old(deref(var("v"))), int(1)));

    let body_expr = add(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .expect("mut borrow verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Mutable borrow with correct final value should verify"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_identity_verified() {
    // Verify that resolve(v) is trivially true when final_value == current_value.
    //
    // fn identity_ref(v: &mut i32) { /* no-op */ }
    // requires: true
    // ensures: resolve(v)  [which expands to v_current == v_final]
    //
    // Body doesn't change v, so final_value = *v = v_current.
    // resolve(v) expands to v_current == v_final, which is v_current == v_current. QED.
    let ens = logic_fn_call("resolve", vec![var("v")]);

    let body_expr = deref(var("v"));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .expect("resolve identity verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve(v) should be trivially true when body is identity: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_fails_when_value_changes() {
    // Verify that resolve(v) FAILS when the body modifies v.
    //
    // fn increment_ref(v: &mut i32) { *v += 1; }
    // requires: true
    // ensures: resolve(v)  [v_current == v_final]
    //
    // Body changes v, so v_final = v_current + 1 != v_current. Should fail.
    let ens = logic_fn_call("resolve", vec![var("v")]);

    let body_expr = add(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .expect("resolve modification verification should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "resolve(v) should fail when body modifies v: {result:?}"
    );
}

/// Verify that resolve(*v) produces the same result as resolve(v) after
/// the Deref-unwrapping fix (#508).
///
/// Before the fix, resolve(Deref(Var("v"))) would produce
/// `v_current_current == v_current_final` (wrong double-wrapping).
/// After the fix, it correctly unwraps to produce `v_current == v_final`.
///
/// We verify this by running the identity-ref scenario with resolve(*v)
/// instead of resolve(v) — both should verify.
#[test]
#[timeout(30000)]
fn test_resolve_deref_var_equivalent_to_resolve_var() {
    // Same setup as test_resolve_identity_verified, but using resolve(*v)
    // instead of resolve(v).
    //
    // fn identity_ref(v: &mut i32) { /* no-op */ }
    // ensures: resolve(*v)
    //
    // With the fix, resolve(*v) unwraps Deref to Var("v"), producing
    // the same v_current == v_final constraint as resolve(v).
    let ens = logic_fn_call("resolve", vec![deref(var("v"))]);

    let body_expr = deref(var("v"));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .expect("resolve(*v) verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve(*v) should verify for identity body (same as resolve(v)): {result:?}"
    );
}

/// Verify that resolve(**v) (nested Deref) still produces correct results.
///
/// The Deref-stripping loop should handle arbitrary nesting depth.
#[test]
#[timeout(30000)]
fn test_resolve_nested_deref_var_equivalent() {
    // resolve(**v) — double deref — should still produce v_current == v_final
    let ens = logic_fn_call("resolve", vec![deref(deref(var("v")))]);

    let body_expr = deref(var("v"));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .expect("resolve(**v) verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve(**v) should verify for identity body (strips all Deref layers): {result:?}"
    );
}

/// Verify that resolve(*v) correctly fails when the body modifies v.
///
/// This is the negative case for the #508 fix — if the Deref unwrapping
/// were wrong (e.g., stripping too aggressively), this test would catch it.
#[test]
#[timeout(30000)]
fn test_resolve_deref_var_fails_when_value_changes() {
    // fn increment_ref(v: &mut i32) { *v += 1; }
    // ensures: resolve(*v)
    //
    // Body changes v, so v_final = v_current + 1. resolve(*v) → v_current == v_final → FAILS.
    let ens = logic_fn_call("resolve", vec![deref(var("v"))]);

    let body_expr = add(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .expect("resolve(*v) modification verification should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "resolve(*v) should fail when body modifies v: {result:?}"
    );
}

/// Verify that resolve(x) returns true for a by-value parameter that has no
/// _final variable in the environment. (#2683)
///
/// In Creusot semantics, `resolve` on a non-mutable-reference (by-value)
/// parameter is vacuously true — there is no borrow to resolve. Before the
/// fix, the encoder would create unconstrained `x_final` variables, causing
/// spurious counterexamples.
#[test]
#[timeout(30000)]
fn test_resolve_by_value_is_true() {
    // Create an encoder with only a bare `x` variable (no `x_final`).
    // This simulates a by-value parameter.
    let mut encoder = AYEncoder::new();

    // Declare only `x` (a by-value parameter — no _current or _final).
    encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .expect("declare x");

    // resolve(x) should encode as `true` since there's no x_final.
    let expr = logic_fn_call("resolve", vec![var("x")]);
    let term = encoder
        .encode_pure(&expr)
        .expect("resolve(x) by-value should encode without error");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Bool,
        "resolve should be Bool-sorted"
    );

    // Assert NOT resolve(x) — should be UNSAT (resolve == true).
    let not_term = encoder.solver.not(term);
    encoder.assert_term(not_term);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_)),
        "NOT resolve(x) should be UNSAT when x is by-value (resolve == true)"
    );
}

/// Verify that resolve(x) still works correctly when x_final IS present
/// (the mutable borrow case). The by-value short-circuit must not break
/// the existing _final-present path. (#2683)
#[test]
#[timeout(30000)]
fn test_resolve_with_final_present_still_constrains() {
    let mut encoder = AYEncoder::new();

    // Declare both x_current and x_final (mutable borrow parameter).
    encoder
        .get_or_declare_var("x", ay_dpll::api::Sort::Int)
        .expect("declare x");
    encoder
        .get_or_declare_var("x_current", ay_dpll::api::Sort::Int)
        .expect("declare x_current");
    encoder
        .get_or_declare_var("x_final", ay_dpll::api::Sort::Int)
        .expect("declare x_final");

    // resolve(x) should generate x_current == x_final (not just true).
    let expr = logic_fn_call("resolve", vec![var("x")]);
    let term = encoder
        .encode_pure(&expr)
        .expect("resolve(x) with _final should encode");

    // Force x_current != x_final, then assert resolve(x) → should be UNSAT
    // (because resolve says they're equal but we forced them unequal).
    let x_current = encoder.var_term("x_current").unwrap();
    let x_final = encoder.var_term("x_final").unwrap();
    let eq_term = encoder.eq_term(x_current, x_final);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    encoder.assert_term(term);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_)),
        "resolve(x) with x_current != x_final forced should be UNSAT"
    );
}
