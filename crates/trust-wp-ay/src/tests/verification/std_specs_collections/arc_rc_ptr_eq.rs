// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Rc/Arc ptr_eq with inner-value biconditional: different values → !ptr_eq is provable.
///
/// Models arc_and_rc.rs line 18-21:
///   let rc3 = Arc::new(2);
///   let b2 = Rc::ptr_eq(&rc, &rc3);
///   proof_assert!(!b2);
///
/// With biconditional `result == (*self == *rhs)`:
/// *rc == 1 and *rc3 == 2, so *rc != *rc3, so result == false.
///
/// Part of #1600, Part of #1572
#[test]
#[timeout(30000)]
fn test_verify_ptr_eq_different_values_provably_false() {
    // Arc::new(1): *rc == 1
    let rc_inner = eq(deref(var("rc")), int(1));
    // Arc::new(2): *rc3 == 2
    let rc3_inner = eq(deref(var("rc3")), int(2));

    // Inner-value biconditional ptr_eq spec: result == (*rc == *rc3)
    let ptr_eq_spec = eq(
        var("ptr_eq_result"),
        eq(deref(var("rc")), deref(var("rc3"))),
    );

    // We want to prove: !ptr_eq_result
    let ens = not(var("ptr_eq_result"));

    let body = not(var("ptr_eq_result"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[rc_inner, rc3_inner, ptr_eq_spec], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "ptr_eq should be provably false when inner values differ: {result:?}"
    );
}
