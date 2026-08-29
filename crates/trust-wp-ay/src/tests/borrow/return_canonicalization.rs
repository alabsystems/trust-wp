// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ntest::timeout;

use super::*;

// --- Bare Var canonicalization tests (#431) ---

/// Test that `result == old(*x)` verifies when `return_expr` uses bare Var. (#431)
///
/// Models: `fn snapshot_example(x: &mut i32) -> i32 { let val = *x; *x += 1; val }`
///   ensures: result == old(*x)
///
/// MIR extraction collapses `*x` to bare `Var("x")` in the return expression,
/// but `old(*x)` encodes to `x_current`. The canonicalization in
/// `verify_mut_borrow_function` wraps bare `Var("x")` in `Deref` to produce
/// `x_current`, matching the postcondition encoding.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_return_old_value_bare_var() {
    // ensures: result == old(*x)
    let ens = eq(var("result"), old(deref(var("x"))));

    // body: x_final = *x + 1 (the mutation)
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: bare Var("x") -- MIR extraction collapsed the deref.
    // Canonicalization wraps this in Deref, producing x_current.
    let return_expr = var("x");

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result == old(*x) with bare Var return should verify: got {result:?}"
    );
}

/// Negative test: wrong postcondition still fails with Var canonicalization. (#431)
///
/// Models: `fn snapshot_example(x: &mut i32) -> i32 { let val = *x; *x += 1; val }`
///   ensures: result == old(*x) + 1 (WRONG -- body returns old value, not old + 1)
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_return_old_value_wrong_post() {
    // WRONG: result == old(*x) + 1 (should be old(*x))
    let ens = eq(var("result"), add(old(deref(var("x"))), int(1)));

    // body: x_final = *x + 1
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: bare Var("x") -- returns old value
    let return_expr = var("x");

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong postcondition on bare Var return should fail: got {result:?}"
    );
}

/// Test that bare Var inside a compound return expression is canonicalized. (#431)
///
/// Models: `fn inc_and_return(x: &mut i32) -> i32 { let old = *x; *x += 2; old + 1 }`
///   ensures: result == old(*x) + 1
///
/// Return expression is `BinOp(Var("x"), Add, Int(1))` -- the `Var("x")` inside
/// the `BinOp` must also be wrapped in Deref.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_return_compound_bare_var() {
    // ensures: result == old(*x) + 1
    let ens = eq(var("result"), add(old(deref(var("x"))), int(1)));

    // body: x_final = *x + 2
    let body_expr = add(deref(var("x")), int(2));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: Var("x") + 1 -- bare Var("x") embedded in BinOp
    let return_expr = add(var("x"), int(1));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "compound return with bare Var should verify: got {result:?}"
    );
}

/// Test the `double_increment` pattern: void function with two mutations. (#533)
///
/// Models: `fn double_increment(x: &mut i32) { *x += 1; *x += 1; }`
///   ensures: *x == old(*x) + 2
///
/// This is the pattern from `simple_examples` that fails with the old Call
/// bailout. After skipping ghost calls, the MIR extraction produces
/// `x_final` = *x + 2, which matches the postcondition.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_double_increment() {
    // ensures: *x_final == old(*x) + 2
    let ens = eq(final_expr(var("x")), add(old(deref(var("x"))), int(2)));

    // body: x_final = *x + 2 (two increments collapsed)
    let body_expr = add(deref(var("x")), int(2));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // No return expression -- void function
    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "double_increment pattern should verify: got {result:?}"
    );
}

/// Negative test: `double_increment` with wrong offset. (#533)
///
/// Models: `fn double_increment(x: &mut i32) { *x += 1; *x += 1; }`
///   ensures: *x == old(*x) + 3  (wrong -- should be +2)
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_double_increment_wrong() {
    // ensures: *x_final == old(*x) + 3 (wrong)
    let ens = eq(final_expr(var("x")), add(old(deref(var("x"))), int(3)));

    // body: x_final = *x + 2
    let body_expr = add(deref(var("x")), int(2));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong double_increment postcondition should fail: got {result:?}"
    );
}

/// Test `Snapshot::capture` value semantics: snapshot binds to captured value. (#547)
///
/// Models: `fn snapshot_return(x: &mut i32) -> i32 {
///     let snap = snapshot!(*x);  // snap = *x at capture site
///     *x += 1;
///     snap                       // return captured value (via Deref of snapshot)
/// }`
///   ensures: result == old(*x)
///
/// After #547 fix, MIR extraction binds the snapshot destination to the
/// captured expression (Deref(Var("x"))) instead of an opaque _`call_N`.
/// The return expression uses the snapshot value, which resolves to *x.
#[test]
#[timeout(30000)]
fn test_verify_snapshot_capture_return_value() {
    // ensures: result == old(*x)
    let ens = eq(var("result"), old(deref(var("x"))));

    // body: x_final = *x + 1
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: Deref(Var("x")) -- the snapshot value after #547 fix.
    // Before #547: this was Var("_call_N") (opaque, verification fails).
    // After #547: bound to Deref(Var("x")), resolves to x_current.
    let return_expr = deref(var("x"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "snapshot capture return value should verify: got {result:?}"
    );
}

/// Negative test: snapshot value after mutation should not match old(*x). (#547)
///
/// Models the case where someone incorrectly returns the post-mutation value
/// instead of the captured pre-mutation value.
#[test]
#[timeout(30000)]
fn test_verify_snapshot_capture_post_mutation_fails() {
    // ensures: result == old(*x)
    let ens = eq(var("result"), old(deref(var("x"))));

    // body: x_final = *x + 1
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // return_expr: *x + 1 (the post-mutation value, not the snapshot)
    let return_expr = add(deref(var("x")), int(1));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "returning post-mutation value with old(*x) postcondition should fail: got {result:?}"
    );
}
