// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use ntest::timeout;

use super::*;

// --- Bool-sorted _final variable tests (#543) ---

#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_bool_flip() {
    // Verify: fn flip(b: &mut bool) { *b = !*b; }
    // requires: true (no precondition)
    // ensures: ^b == !old(*b)
    // body: b_final = !*b
    let ens = eq(final_expr(var("b")), not(old(deref(var("b")))));

    // body: b_final = !*b (a Bool-sorted expression)
    let body_expr = not(deref(var("b")));
    let mut final_values = HashMap::new();
    final_values.insert("b".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "bool flip should verify with Sort::Bool _final var: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_bool_flip_wrong_post() {
    // Wrong postcondition: ^b == old(*b) (should be !old(*b))
    let ens = eq(final_expr(var("b")), old(deref(var("b"))));

    let body_expr = not(deref(var("b")));
    let mut final_values = HashMap::new();
    final_values.insert("b".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong bool flip postcondition should fail: got {result:?}"
    );
}

/// Test mut-borrow function that returns a Bool. (#544 Phase 1)
///
/// Scenario: `fn was_positive(v: &mut i32) -> bool { let r = *v > 0; *v = 0; r }`
/// requires: true
/// ensures: result == (old(*v) > 0)
/// body: `v_final` = 0, return = (*v > 0)
///
/// The `result` variable must be `Sort::Bool`, not `Sort::Int`, to avoid ay panic
/// on `mk_eq(Int, Bool)` when asserting `result = (*v > 0)`.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_bool_return() {
    // ensures: result == (old(*v) > 0)
    let ens = eq(var("result"), gt(old(deref(var("v"))), int(0)));

    // body effect: v_final = 0
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), int(0));

    // return expression: *v > 0 (Bool)
    let return_expr = gt(deref(var("v")), int(0));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mut-borrow function returning Bool should verify: got {result:?}"
    );
}

/// Negative test: mut-borrow function with wrong Bool return postcondition. (#544 Phase 1)
///
/// ay-dpll reports a concrete counterexample for the mixed Int+Bool return
/// postcondition. (#2141)
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_bool_return_wrong_post() {
    // ensures: result == (old(*v) < 0) -- wrong, should be > 0
    let ens = eq(var("result"), lt(old(deref(var("v"))), int(0)));

    // body effect: v_final = 0
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), int(0));

    // return expression: *v > 0 (Bool)
    let return_expr = gt(deref(var("v")), int(0));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    match result {
        VerificationResult::Failed(cex) => {
            assert_eq!(
                cex.bool_assignments()
                    .find_map(|(name, value)| (name == "result").then_some(value)),
                Some(false),
                "counterexample should set result=false: {cex:?}"
            );
            assert_eq!(
                cex.int_assignments()
                    .find_map(|(name, value)| (name == "old_v_current").then_some(value)),
                Some(-1),
                "counterexample should use old_v_current=-1: {cex:?}"
            );
        }
        other => panic!("wrong Bool return postcondition should fail: got {other:?}"),
    }
}

// --- canonicalize_mut_ref_vars recursion tests (#598) ---

/// Test that `canonicalize_mut_ref_vars` recurses into `Let` expressions.
///
/// Models: `fn let_return(x: &mut i32) -> i32 { let t = *x; *x += 1; t }`
///   ensures: result == old(*x)
///
/// MIR extraction may produce `Let { var: "t", value: Var("x"), body: Var("t") }`
/// as the return expression. The bare `Var("x")` inside the `Let` value is
/// canonicalized to `Deref(Var("x"))`, mapping to `x_current` in SMT.
#[test]
#[timeout(30000)]
fn test_canonicalize_mut_ref_let_recursion() {
    // ensures: result == old(*x)
    let ens = eq(var("result"), old(deref(var("x"))));

    // body: x_final = *x + 1
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: Let { t = Var("x"), body = Var("t") }
    // canonicalize_mut_ref_vars recurses into Let, wrapping Var("x") in
    // Deref so it encodes as `x_current` (matching the postcondition).
    let return_expr = let_bind("t", var("x"), var("t"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    );

    match &result {
        Ok(VerificationResult::Verified(_)) => {
            // Expected: Let value Var("x") is canonicalized to Deref(Var("x")),
            // encoding as `x_current`, matching the postcondition `old(*x)`.
        }
        other => {
            panic!("Expected Verified after Let recursion fix (#598), got: {other:?}");
        }
    }
}

/// Test that `canonicalize_mut_ref_vars` recurses into `LogicFnCall` args.
///
/// The return expression contains `LogicFnCall { name: "identity", args: [Var("x")] }`
/// where x is a mut-ref param. After canonicalization, `Var("x")` becomes
/// `Deref(Var("x"))` encoding as `x_current`. The `identity` function is
/// uninterpreted (no axiom), so the verification result is Unknown/Failed,
/// but the encoding must not panic. (#598)
#[test]
#[timeout(30000)]
fn test_canonicalize_mut_ref_logic_fn_call_recursion() {
    // ensures: result == old(*x) + 1
    let ens = eq(var("result"), add(old(deref(var("x"))), int(1)));

    // body: x_final = *x + 2
    let body_expr = add(deref(var("x")), int(2));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: LogicFnCall("identity", [Var("x")])
    // Var("x") is now canonicalized to Deref(Var("x")) -> encodes as x_current.
    let return_expr = logic_fn_call("identity", vec![var("x")]);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    );

    assert!(
        result.is_ok(),
        "LogicFnCall with canonicalized Var should not cause encoding panic: {result:?}"
    );
    // identity() is uninterpreted (no axiom). The postcondition must not
    // verify; depending on solver completeness this is either a counterexample
    // or an incomplete result.
    let vr = result.unwrap();
    assert!(
        matches!(
            vr,
            VerificationResult::Failed(_) | VerificationResult::Unknown(UnknownReason::Incomplete)
        ),
        "Uninterpreted identity call should not verify, got {vr:?}"
    );
}

/// Test that `canonicalize_mut_ref_vars` recurses into `View` expressions.
///
/// Models: `fn view_return(v: &mut Vec<i32>) -> Seq<i32> { v@ }`
///   ensures: result == old(v@)
///
/// The return expression `View(Var("v"))` must have `Var("v")` canonicalized
/// to `Deref(Var("v"))` so it encodes as `v_current` in SMT. (#598)
#[test]
#[timeout(30000)]
fn test_canonicalize_mut_ref_view_recursion() {
    // ensures: result@ == old(*v)@  (simplified as view of deref)
    let ens = eq(var("result"), old(view(deref(var("v")))));

    // body: v_final = *v (identity for simplicity)
    let body_expr = deref(var("v"));
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    // return_expr: View(Var("v"))
    // Var("v") is now canonicalized to Deref(Var("v")) -> encodes as v_current.
    let return_expr = view(var("v"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    );

    // View encoding may produce a UF call; we just verify no encoding panic.
    assert!(
        result.is_ok(),
        "View with canonicalized Var should not cause encoding panic: {result:?}"
    );
    // `verify_mut_borrow_function` now aliases `old_{name}_current_view` to
    // `{name}_current_view`, so this identity body verifies successfully.
    //
    // KNOWN-CLASS PIN (2026-08-23 mut_ref drift adjudication): since ay's
    // mandatory strict UNSAT certification (0.7 line), this VC computes UNSAT
    // but its certificate carries an unverified premiseless trust step
    // ("step t0 uses unverified trust rule"), so the Verified demotes to
    // `Unknown(ProofTrusted)` — the sound direction. The encoding property
    // this test guards is intact; the gap is upstream certificate coverage
    // (ay docs/ay-asks 2026-08-23 premiseless-Trust census). Retire the
    // `ProofTrusted` tolerance when the class closes upstream and this VC
    // certifies again. Every other outcome (Failed/CE, other Unknowns) still
    // fails the test.
    let vr = result.unwrap();
    assert!(
        matches!(
            vr,
            VerificationResult::Verified(_)
                | VerificationResult::Unknown(UnknownReason::ProofTrusted)
        ),
        "view recursion with old/current aliasing should verify (or demote to \
         the known proof-trusted certification gap), got {vr:?}"
    );
}

/// Test that `canonicalize_mut_ref_vars` correctly handles variable shadowing
/// in `Let` bindings.
///
/// When a `Let` binds a variable with the same name as a mut-ref param,
/// uses of that variable inside the body should NOT be canonicalized
/// (i.e., should NOT be wrapped in `Deref`), because the let-bound variable
/// shadows the outer param.
///
/// Without shadowing logic, `Var("x")` in the body would be incorrectly
/// wrapped as `Deref(Var("x"))` -> encoding as `x_current` instead of the
/// let-bound value 42. (#598)
#[test]
#[timeout(30000)]
fn test_canonicalize_mut_ref_let_shadowing() {
    // ensures: result == 42
    let ens = eq(var("result"), int(42));

    // body: x_final = *x + 1 (arbitrary mutation)
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: Let { x = 42, body = Var("x") }
    // The inner Var("x") is shadowed by the let binding, so it must NOT
    // be canonicalized to Deref(Var("x")). It should encode as the literal
    // 42, not as x_current.
    let return_expr = let_bind("x", int(42), var("x"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    );

    match &result {
        Ok(VerificationResult::Verified(_)) => {
            // Expected: Let body Var("x") is NOT canonicalized because "x" is
            // shadowed by the let binding. The return value is 42, matching
            // the postcondition.
        }
        other => {
            panic!(
                "Expected Verified for let-shadowed variable (#598), got: {other:?}. \
                 If Failed/Unknown, the shadowing logic in canonicalize_mut_ref_vars \
                 may be broken -- Var(\"x\") in the body was likely incorrectly wrapped \
                 in Deref, encoding as x_current instead of 42."
            );
        }
    }
}

/// Test that `canonicalize_mut_ref_vars` correctly handles Match arm pattern
/// bindings that shadow mut-ref params.
///
/// Scenario: mut-ref param `x`, return expression is
/// `match *x { x => x + 1 }`. The `x` in the pattern binding shadows
/// the outer mut-ref param, so `Var("x")` in the arm body should NOT be
/// wrapped in `Deref`. (#598, #607)
#[test]
#[timeout(30000)]
fn test_canonicalize_mut_ref_match_arm_shadowing() {
    // ensures: result == *x + 1  (i.e., x_current + 1)
    let ens = eq(var("result"), add(deref(var("x")), int(1)));

    // body: x_final = *x (identity mutation for simplicity)
    let body_expr = deref(var("x"));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: match *x { x => x + 1 }
    // The Binding("x") in the match arm shadows the mut-ref param "x",
    // so arm body Var("x") must NOT be canonicalized to Deref(Var("x")).
    // The arm body evaluates to (pattern-bound x) + 1, which equals *x + 1.
    let return_expr = match_expr(
        deref(var("x")),
        vec![(Pattern::Binding("x".to_string()), add(var("x"), int(1)))],
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    );

    match &result {
        Ok(VerificationResult::Verified(_)) => {
            // Expected: Match arm Binding("x") shadows the mut-ref param,
            // so arm body Var("x") is the pattern-bound value (== *x).
            // result == *x + 1 matches the postcondition.
        }
        other => {
            panic!(
                "Expected Verified for match-arm-shadowed variable (#607), got: {other:?}. \
                 If Failed/Unknown, the Match arm pattern shadowing in \
                 canonicalize_mut_ref_vars may be broken -- Var(\"x\") in the arm body \
                 was likely incorrectly wrapped in Deref."
            );
        }
    }
}

/// Regression test for take_max flapping verification (#609).
///
/// Models the Creusot `take_max` function:
/// ```text
/// #[ensures(if *ma >= *mb { *mb == ^mb && result == ma }
///                    else { *ma == ^ma && result == mb })]
/// fn take_max(ma: &mut u32, mb: &mut u32) -> &mut u32 {
///     if *ma >= *mb { ma } else { mb }
/// }
/// ```
///
/// Before the fix, bare `Var("ma")` in `result == ma` produced an
/// unconstrained SMT variable, causing non-deterministic verification.
#[test]
#[timeout(30000)]
fn test_verify_take_max_reference_equality() {
    // requires: (none)
    // The postcondition as parsed (before transform):
    // if *ma >= *mb { *mb == ^mb && result == ma }
    //           else { *ma == ^ma && result == mb }
    let postcond_raw = ite(
        ge(deref(var("ma")), deref(var("mb"))),
        // then: *mb == ^mb && result == ma
        and(
            eq(deref(var("mb")), final_expr(var("mb"))),
            eq(var("result"), var("ma")),
        ),
        // else: *ma == ^ma && result == mb
        and(
            eq(deref(var("ma")), final_expr(var("ma"))),
            eq(var("result"), var("mb")),
        ),
    );

    // Apply the postcondition transformation (as the driver does)
    let mut_ref_params: HashSet<String> =
        ["ma".to_string(), "mb".to_string()].into_iter().collect();
    let postcond = postcond_raw.transform_postcondition_for_mut_refs(&mut_ref_params);

    // final_values: take_max doesn't modify values, both branches have same result.
    // ma_final = ite(ma_current >= mb_current, ma_current, ma_current) = ma_current
    // mb_final = ite(ma_current >= mb_current, mb_current, mb_current) = mb_current
    let cond = ge(deref(var("ma")), deref(var("mb")));
    let ma_final_expr = ite(cond.clone(), deref(var("ma")), deref(var("ma")));
    let mb_final_expr = ite(cond.clone(), deref(var("mb")), deref(var("mb")));

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), ma_final_expr);
    final_values.insert("mb".to_string(), mb_final_expr);

    // return_expr: if *ma >= *mb { ma } else { mb } (bare Var -- MIR style)
    let return_expr = ite(cond, var("ma"), var("mb"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[postcond], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "take_max reference equality should verify deterministically: got {result:?}. \
         If Failed, bare Var(\"ma\"/\"mb\") in postcondition may be producing \
         unconstrained SMT variables instead of mapping to _current."
    );
}

/// Negative test: wrong reference returned in take_max postcondition (#609).
///
/// Swaps `result == ma` / `result == mb` in the branches so the postcondition
/// claims the opposite reference is returned. This must fail to ensure the
/// bare-Var fix doesn't weaken the verification.
#[test]
#[timeout(30000)]
fn test_verify_take_max_wrong_ref_fails() {
    // Same structure as take_max but with SWAPPED result == mb / result == ma
    // Then: *ma >= *mb -> result == mb (WRONG -- should be ma)
    // Else: result == ma (WRONG -- should be mb)
    let postcond_raw = ite(
        ge(deref(var("ma")), deref(var("mb"))),
        // then: *mb == ^mb && result == mb (WRONG: should be ma)
        and(
            eq(deref(var("mb")), final_expr(var("mb"))),
            eq(var("result"), var("mb")),
        ),
        // else: *ma == ^ma && result == ma (WRONG: should be mb)
        and(
            eq(deref(var("ma")), final_expr(var("ma"))),
            eq(var("result"), var("ma")),
        ),
    );

    let mut_ref_params: HashSet<String> =
        ["ma".to_string(), "mb".to_string()].into_iter().collect();
    let postcond = postcond_raw.transform_postcondition_for_mut_refs(&mut_ref_params);

    let cond = ge(deref(var("ma")), deref(var("mb")));
    let ma_final_expr = ite(cond.clone(), deref(var("ma")), deref(var("ma")));
    let mb_final_expr = ite(cond.clone(), deref(var("mb")), deref(var("mb")));

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), ma_final_expr);
    final_values.insert("mb".to_string(), mb_final_expr);

    let return_expr = ite(cond, var("ma"), var("mb"));

    // Precondition: *ma != *mb (so the two references are distinguishable)
    let requires = ne(deref(var("ma")), deref(var("mb")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[requires], &[postcond], &final_values)
            .return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "take_max with swapped references (given ma != mb) should FAIL: got {result:?}. \
         If Verified, the bare-Var encoding may be too weak (accepting wrong contracts)."
    );
}
