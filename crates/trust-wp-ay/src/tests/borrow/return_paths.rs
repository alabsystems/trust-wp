// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ntest::timeout;

use super::*;

// ============================================================================
// Coverage gap tests: return_expr, multiple final_values, empty ensures
// ============================================================================

/// Test `verify_mut_borrow_function` with `return_expr` (mut ref + return value).
///
/// Models: `fn pop_and_return_len(v: &mut Vec<T>) -> usize { v.pop(); v.len() }`
/// Simplified to integer domain:
///   fn `decrement_and_return(v`: &mut i32) -> i32 { *v -= 1; *v }
///   requires: *v > 0
///   ensures: result == old(*v) - 1
///   ensures: ^v == old(*v) - 1
///
/// Exercises the `return_expr` path at verify.rs:550-555 which was previously
/// untested (all prior borrow tests pass `None` for `return_expr`).
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_with_return_expr() {
    // requires: *v > 0
    let req = gt(deref(var("v")), int(0));

    // ensures: result == old(*v) - 1
    let ens_result = eq(var("result"), sub(old(deref(var("v"))), int(1)));

    // ensures: ^v == old(*v) - 1
    let ens_final = eq(final_expr(var("v")), sub(old(deref(var("v"))), int(1)));

    // body effect: v_final = *v - 1
    let body_expr = sub(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr.clone());

    // return_expr: the function returns *v - 1 (same as body effect)
    let return_expr = body_expr;

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req], &[ens_result, ens_final], &final_values)
            .return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mut borrow with return_expr should verify: got {result:?}"
    );
}

/// Test `verify_mut_borrow_function` with wrong `return_expr` postcondition.
///
/// The return expression is correct but the postcondition claims result == old(*v).
/// Since the body returns *v - 1, this should fail.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_with_return_expr_wrong_post() {
    let req = gt(deref(var("v")), int(0));

    // WRONG: result == old(*v) (should be old(*v) - 1)
    let ens = eq(var("result"), old(deref(var("v"))));

    let body_expr = sub(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr.clone());
    let return_expr = body_expr;

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong return postcondition should fail: got {result:?}"
    );
}

/// Test `verify_mut_borrow_function` with multiple `final_values`.
///
/// Models: `fn swap(a: &mut i32, b: &mut i32) { let t = *a; *a = *b; *b = t; }`
///   ensures: ^a == old(*b)
///   ensures: ^b == old(*a)
///
/// Exercises the loop at verify.rs:536-547 with 2 entries.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_swap_two_refs() {
    let req = bool_expr(true);

    // ensures: ^a == old(*b)
    let ens_a = eq(final_expr(var("a")), old(deref(var("b"))));

    // ensures: ^b == old(*a)
    let ens_b = eq(final_expr(var("b")), old(deref(var("a"))));

    // body: a_final = *b, b_final = *a
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var("b")));
    final_values.insert("b".to_string(), deref(var("a")));

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &[req],
        &[ens_a, ens_b],
        &final_values,
    ))
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "swap with two &mut refs should verify: got {result:?}"
    );
}

/// Test `verify_mut_borrow_function` with empty ensures (early return path).
///
/// When ensures is empty, the function should return Verified immediately
/// (line 558-559 of verify.rs) without checking satisfiability.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_empty_ensures() {
    let req = gt(deref(var("v")), int(0));

    let body_expr = add(deref(var("v")), int(1));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), body_expr);

    // Empty ensures -> should return Verified immediately
    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "empty ensures should verify trivially: got {result:?}"
    );
}

// --- Integration tests: postcondition_mut through verify_mut_borrow_function (#525) ---

/// Integration test: `postcondition_mut` UF call in requires + prophecy encoding
/// through the full `verify_mut_borrow_function` solver pipeline.
///
/// Models:
/// ```rust
/// fn apply_mut<F: FnMut(i32) -> i32>(f: &mut F, v: &mut i32) {
///     *v = (*f)(*v);
/// }
/// ```
///
/// The driver would produce:
///   `call_assumption` (merged into requires):
///     (*`f).postcondition_mut`(*v, ^f, `call_0`) -- closure was called, result is `call_0`
///   ensures: ^v == `call_0` -- final value of v equals closure call result
///   `final_values`: v -> `call_0`, f -> ^f
///
/// This exercises the interaction between:
/// - `postcondition_mut` UF symbol declaration (encoder)
/// - Final/prophecy variable encoding (`v_final`, `f_final`)
/// - Quantifier mode activation (`has_closure_specs` detection)
/// - Solver roundtrip through ay
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_postcondition_mut_integration() {
    // call_assumption: (*f).postcondition_mut(*v, ^f, call_0)
    // This is a Bool-valued uninterpreted function: postcondition_mut(f, v_current, f_final, call_0)
    let call_assumption = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![
            deref(var("v")),      // *v (argument)
            final_expr(var("f")), // ^f (post-state)
            var("call_0"),        // result of closure call
        ],
    );

    // ensures: ^v == call_0
    let ens = eq(final_expr(var("v")), var("call_0"));

    // final_values: v_final = call_0 (assigned the closure result)
    //               f_final = ^f (closure borrow ends)
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), var("call_0"));
    final_values.insert("f".to_string(), final_expr(var("f")));

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &[call_assumption],
        &[ens],
        &final_values,
    ))
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition_mut through mut borrow pipeline should verify: got {result:?}"
    );
}

/// Negative test: wrong postcondition with `postcondition_mut` through
/// `verify_mut_borrow_function`.
///
/// Same model as above but ensures claims `^v == call_0 + 1` (WRONG).
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_postcondition_mut_wrong_ensures() {
    // call_assumption: (*f).postcondition_mut(*v, ^f, call_0)
    let call_assumption = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![deref(var("v")), final_expr(var("f")), var("call_0")],
    );

    // WRONG ensures: ^v == call_0 + 1 (body sets v_final = call_0, not call_0 + 1)
    let ens = eq(final_expr(var("v")), add(var("call_0"), int(1)));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), var("call_0"));
    final_values.insert("f".to_string(), final_expr(var("f")));

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &[call_assumption],
        &[ens],
        &final_values,
    ))
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong postcondition with postcondition_mut should fail: got {result:?}"
    );
}

/// Integration test: `postcondition_mut` with return value through
/// `verify_mut_borrow_function`.
///
/// Models:
/// ```rust
/// fn call_and_return<F: FnMut(i32) -> i32>(f: &mut F, v: &mut i32) -> i32 {
///     let r = (*f)(*v);
///     *v = r;
///     r // returns the closure result
/// }
/// ```
///
/// requires (`call_assumption)`: (*`f).postcondition_mut`(*v, ^f, `call_0`)
/// ensures: ^v == `call_0` && result == `call_0`
/// `final_values`: v -> `call_0`, f -> ^f
/// `return_expr`: `call_0`
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_postcondition_mut_with_return() {
    let call_assumption = method_call(
        deref(var("f")),
        "postcondition_mut",
        vec![deref(var("v")), final_expr(var("f")), var("call_0")],
    );

    // ensures[0]: ^v == call_0
    let ens_final_v = eq(final_expr(var("v")), var("call_0"));

    // ensures[1]: result == call_0
    let ens_result = eq(var("result"), var("call_0"));

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), var("call_0"));
    final_values.insert("f".to_string(), final_expr(var("f")));

    let return_expr = var("call_0");

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(
            &[call_assumption],
            &[ens_final_v, ens_result],
            &final_values,
        )
        .return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition_mut with return through mut borrow pipeline should verify: got {result:?}"
    );
}
