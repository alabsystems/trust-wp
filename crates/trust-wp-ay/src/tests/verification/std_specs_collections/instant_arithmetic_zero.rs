// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Instant + Duration encoding: adding zero duration yields the same instant.
///
/// Models: `instant + Duration::from_secs(0) == instant`
/// Uses the Instant Add<Duration> spec: `result@ == self@ + rhs@`
/// and Duration from_secs(0) spec: `result@ == 0`.
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_instant_add_zero_duration_identity() {
    // Call-site assumption from Instant::now(): instant@ >= 0
    let now_assumption = ge(var("instant"), int(0));

    // Call-site assumption from Duration::from_secs(0): zero_dur@ == 0
    let zero_dur_assumption = eq(var("zero_dur"), int(0));

    // Call-site assumption from Instant + Duration:
    //   add_result@ == instant@ + zero_dur@
    let add_assumption = eq(var("add_result"), add(var("instant"), var("zero_dur")));

    // ensures: add_result@ == instant@ (the assert! equality check)
    let ens = eq(var("add_result"), var("instant"));

    let body = var("add_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[now_assumption, zero_dur_assumption, add_assumption],
            &[ens],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "instant + zero_duration == instant should verify: {result:?}"
    );
}

/// Instant subtraction encoding: instant - instant == zero duration.
///
/// Models: `instant - instant == zero_dur` where zero_dur@ == 0.
/// Uses SUB_COMBINED spec: `self@ >= rhs@ ==> result@ == self@ - rhs@`
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_instant_sub_self_is_zero() {
    // instant@ >= 0
    let now_assumption = ge(var("instant"), int(0));

    // zero_dur@ == 0
    let zero_dur_assumption = eq(var("zero_dur"), int(0));

    // SUB_COMBINED clause 1: self@ >= rhs@ ==> result@ == self@ - rhs@
    // With self == rhs == instant: instant@ >= instant@ ==> sub_result@ == 0
    let sub_assumption = implies(
        ge(var("instant"), var("instant")),
        eq(var("sub_result"), sub(var("instant"), var("instant"))),
    );

    // ensures: sub_result@ == zero_dur@ (the assert! equality check)
    let ens = eq(var("sub_result"), var("zero_dur"));
    let body = var("sub_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[now_assumption, zero_dur_assumption, sub_assumption],
            &[ens],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "instant - instant == zero_duration should verify: {result:?}"
    );
}
