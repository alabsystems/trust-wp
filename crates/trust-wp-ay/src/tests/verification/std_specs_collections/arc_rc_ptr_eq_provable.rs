// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Rc/Arc ptr_eq soundness limitation: same inner values, distinct allocations →
/// ptr_eq IS provable (known over-approximation).
///
/// With the inner-value biconditional `result == (*self == *rhs)`, two distinct
/// Arc::new(42) allocations with equal inner values will prove ptr_eq == true.
/// This is over-strong (unsound for this specific pattern), but a fully sound
/// model requires allocation identity tracking not yet in the SMT encoding.
///
/// This test documents the known limitation.
///
/// Part of #1600, Part of #1572
#[test]
#[timeout(30000)]
fn test_verify_ptr_eq_same_value_is_provable_known_limitation() {
    // Two Rc values with the same inner value (distinct allocations)
    let rc_inner = eq(deref(var("rc")), int(42));
    let rc2_inner = eq(deref(var("rc2")), int(42));

    // Inner-value biconditional: result == (*rc == *rc2)
    // Since *rc == 42 == *rc2, this gives result == true
    let ptr_eq_spec = eq(
        var("ptr_eq_result"),
        eq(deref(var("rc")), deref(var("rc2"))),
    );

    let ens = var("ptr_eq_result");
    let body = var("ptr_eq_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[rc_inner, rc2_inner, ptr_eq_spec], &[ens])
            .return_expr(Some(&body)),
    );
    // Known limitation: inner-value biconditional proves this (over-approximation)
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "ptr_eq should be provable with same inner values (known over-approx): {result:?}"
    );
}

/// Rc/Arc clone + ptr_eq: clone preserves inner value → ptr_eq provable.
///
/// Models arc_and_rc.rs line 12-17:
///   let rc2 = rc.clone();
///   let b = Rc::ptr_eq(&rc, &rc2);
///   proof_assert!(b);
///
/// Clone spec gives `*rc2 == *rc` (inner-value equality).
/// Inner-value biconditional ptr_eq: `result == (*rc == *rc2)`.
/// Since `*rc == *rc2`, result == true. QED.
///
/// Part of #1572
#[test]
#[timeout(30000)]
fn test_verify_clone_then_ptr_eq_provable() {
    // Clone spec: *rc2 == *rc (inner-value equality from clone postcondition)
    let clone_spec = eq(deref(var("rc2")), deref(var("rc")));

    // Inner-value biconditional ptr_eq spec: result == (*rc == *rc2)
    let ptr_eq_spec = eq(
        var("ptr_eq_result"),
        eq(deref(var("rc")), deref(var("rc2"))),
    );

    let ens = var("ptr_eq_result");
    let body = var("ptr_eq_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[clone_spec, ptr_eq_spec], &[ens]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "ptr_eq should be provable after clone (inner values equal): {result:?}"
    );
}
