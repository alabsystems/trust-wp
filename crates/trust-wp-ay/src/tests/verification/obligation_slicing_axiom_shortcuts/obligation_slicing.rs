// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
// ── Obligation slicing tests (#994) ─────────────────────────────────

/// Multiple independent postconditions should all verify via per-slice solving.
#[test]
#[timeout(30000)]
fn test_obligation_slicing_multiple_ensures_all_verify() {
    // requires: x > 0
    // ensures: result > 0, result > x - 1, result == x + 1
    // body: x + 1
    let req = gt(var("x"), int(0));
    let ens1 = gt(var("result"), int(0));
    let ens2 = gt(var("result"), sub(var("x"), int(1)));
    let ens3 = eq(var("result"), add(var("x"), int(1)));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens1, ens2, ens3]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "all three postconditions should verify independently: {result:?}"
    );
}

/// When one postcondition fails, overall result is Failed even if others verify.
#[test]
#[timeout(30000)]
fn test_obligation_slicing_one_fails_overall_fails() {
    // requires: x > 0
    // ensures: result > 0, result < 0  (second is false)
    // body: x + 1
    let req = gt(var("x"), int(0));
    let ens_ok = gt(var("result"), int(0));
    let ens_bad = lt(var("result"), int(0));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens_ok, ens_bad]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "should fail because result < 0 is false for x+1 with x > 0: {result:?}"
    );
}

/// Single postcondition still works correctly (no slice loop regression).
#[test]
#[timeout(30000)]
fn test_obligation_slicing_single_ensure() {
    let req = gt(var("x"), int(0));
    let ens = gt(var("result"), var("x"));
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "single postcondition should verify: {result:?}"
    );
}

/// Empty ensures means trivially verified (no slices to check).
#[test]
#[timeout(30000)]
fn test_obligation_slicing_empty_ensures() {
    let body = int(42);
    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[]).return_expr(Some(&body)))
            .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "no postconditions should be trivially verified: {result:?}"
    );
}

/// Mut-borrow verification also uses per-slice solving.
#[test]
#[timeout(30000)]
fn test_obligation_slicing_mut_borrow_multiple_ensures() {
    let req = gt(deref(var("v")), int(0));
    // ensures: ^v > 0, ^v == *v + 1
    let ens1 = gt(final_expr(var("v")), int(0));
    let ens2 = eq(final_expr(var("v")), add(deref(var("v")), int(1)));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &[req],
        &[ens1, ens2],
        &final_values,
    ))
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mut-borrow per-slice verification should succeed: {result:?}"
    );
}
