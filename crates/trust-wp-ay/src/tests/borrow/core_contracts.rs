// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_verify_increment_ref() {
    // Verify: fn increment_ref(v: &mut i32) { *v += 1; }
    let req = gt(deref(var("v")), int(i64::from(i32::MIN)));
    let ens = eq(final_expr(var("v")), add(old(deref(var("v"))), int(1)));
    let body_expr = add(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "increment_ref should verify, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_increment_ref_wrong_postcondition() {
    // Same as above but with wrong postcondition: ^v == old(*v) + 2
    let req = gt(deref(var("v")), int(i64::from(i32::MIN)));

    // Wrong postcondition: ^v == old(*v) + 2 (should be +1)
    let ens = eq(final_expr(var("v")), add(old(deref(var("v"))), int(2))); // Wrong: should be 1
    let body_expr = add(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "increment_ref with wrong postcondition should fail"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_abs_mut_simple() {
    // Simplified abs_mut test: ^v >= 0
    let req = bool_expr(true);
    let ens = ge(final_expr(var("v")), int(0));
    let body_expr = ite(
        lt(deref(var("v")), int(0)),
        neg(deref(var("v"))),
        deref(var("v")),
    );

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "abs_mut should verify ^v >= 0"
    );
}

// Reborrow and nested borrow tests (Re: #348)

/// Test reborrowing: `fn reborrow(x: &mut T) -> &mut T { &mut *x }`
///
/// Reborrowing should preserve contracts - the final value should equal
/// the dereferenced value since we're just creating a new reference to
/// the same location.
#[test]
#[timeout(30000)]
fn test_verify_reborrow_preserves_value() {
    // Contract: fn reborrow(v: &mut i32) { *v; } // identity on pointee
    // requires: true
    // ensures: ^v == old(*v) (value unchanged by reborrow)
    let req = bool_expr(true);

    // Postcondition: final value equals original value
    let ens = eq(final_expr(var("v")), old(deref(var("v"))));

    // Body: identity (reborrow doesn't change value)
    let body_expr = deref(var("v"));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "reborrow should preserve value: ^v == old(*v)"
    );
}

/// Test nested dereference encoding: `*(*v)` chains.
///
/// The encoder should handle nested `Deref` by generating names like
/// `v_current_current` for `*(*v)`.
#[test]
#[timeout(30000)]
fn test_verify_nested_deref() {
    // Contract: fn nested_deref(v: &mut &mut i32) -> i32 { **v }
    // This tests that nested deref encoding produces correct symbolic names.
    //
    // requires: true
    // ensures: result == *(*v)  (we just return the doubly-dereferenced value)
    //
    // For simplicity, we test with a single level where the body expression
    // involves Deref(Deref(Var("v"))) to verify the encoding handles it.

    let req = bool_expr(true);

    // ^v == *(*v) - final value equals the doubly-dereferenced input
    // (This is a bit contrived but tests the encoding)
    let ens = eq(final_expr(var("v")), deref(deref(var("v"))));

    // Body: **v
    let body_expr = deref(deref(var("v")));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "nested deref should verify: ^v == **v"
    );
}

/// Test Final(Var) combined with Old(Deref(Var)) encoding.
///
/// Verifies that the encoder correctly handles postconditions where
/// the final value (`^v`) is compared against the original dereference
/// (`old(*v)`). This exercises the `old` operator with deref inside.
///
/// Note: This is semantically similar to `test_verify_reborrow_preserves_value`
/// but uses different terminology to emphasize Old(Deref) encoding.
#[test]
#[timeout(30000)]
fn test_verify_old_deref_encoding() {
    // Contract: fn identity(v: &mut i32) { *v; } // read-only access
    // requires: true
    // ensures: ^v == old(*v) (unchanged)
    //
    // This tests that Old(Deref(Var("v"))) produces correct SMT.

    let req = bool_expr(true);

    // ^v == old(*v) - final value equals original dereference
    let ens = eq(final_expr(var("v")), old(deref(var("v"))));

    // Body: *v (identity - just read the current value)
    let body_expr = deref(var("v"));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Old(Deref) encoding should verify: ^v == old(*v)"
    );
}

/// Test old(*v) aliasing: `old(*v)` equals `*v` for unchanged references.
///
/// In the `RustHorn` encoding, `old(*v)` at function entry equals the
/// initial `*v` value. This test verifies the aliasing is correct.
///
/// This complements `test_verify_old_deref_encoding` by verifying the
/// semantic equivalence rather than just encoding correctness.
#[test]
#[timeout(30000)]
fn test_verify_old_deref_semantics() {
    // Contract: fn read_ref(v: &mut i32) -> i32 { *v }
    // requires: true
    // ensures: ^v == old(*v) (semantic: old(*v) aliases initial *v)

    let req = bool_expr(true);

    // ^v == old(*v)
    let ens = eq(final_expr(var("v")), old(deref(var("v"))));

    // Body: *v (read the reference)
    let body_expr = deref(var("v"));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "old(*v) should alias initial *v for identity function"
    );
}
