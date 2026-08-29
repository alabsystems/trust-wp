// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Arc::new and deref identity: *Arc::new(v) == v
///
/// Models the Creusot arc_and_rc.rs test pattern:
///   let rc = Arc::new(1);
///   proof_assert!(*rc@ == 1i32);
///
/// The ARC_NEW/RC_NEW spec is: ensures: *result == value
/// At ay level: arc_inner == value (from new spec), then deref == arc_inner.
///
/// Part of #1075
#[test]
#[timeout(30000)]
fn test_verify_arc_new_deref_identity() {
    // value == 1
    let value_assumption = eq(var("value"), int(1));

    // Arc::new postcondition: *result == value
    // At ay level: arc_inner == value
    let new_assumption = eq(var("arc_inner"), var("value"));

    // ensures: arc_inner == 1
    let ens = eq(var("arc_inner"), int(1));

    let body = var("arc_inner");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[value_assumption, new_assumption], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Arc::new deref identity should verify: {result:?}"
    );
}

/// Arc as_ref preserves inner value: result@ == *self
///
/// Models the second part of Creusot arc_and_rc.rs:
///   let inner = rc.as_ref();
///   proof_assert!(inner@ == 1);
///
/// The ARC_AS_REF spec: ensures: result@ == *self
/// Combined with ARC_NEW: *arc == value, this chain should give inner@ == value.
///
/// Part of #1075
#[test]
#[timeout(30000)]
fn test_verify_arc_as_ref_chain() {
    // value == 2
    let value_assumption = eq(var("value"), int(2));

    // Arc::new postcondition: arc_inner == value
    let new_assumption = eq(var("arc_inner"), var("value"));

    // Arc::as_ref postcondition: as_ref_view == arc_inner
    let as_ref_assumption = eq(var("as_ref_view"), var("arc_inner"));

    // ensures: as_ref_view == 2 (the chained result)
    let ens = eq(var("as_ref_view"), int(2));

    let body = var("as_ref_view");

    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[value_assumption, new_assumption, as_ref_assumption],
            &[ens],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Arc as_ref chain should verify: {result:?}"
    );
}
