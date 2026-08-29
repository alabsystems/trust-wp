// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Duration comparison encoding: elapsed duration >= zero.
///
/// Models: `instant.elapsed() >= zero_dur` where elapsed returns
/// a Duration with view >= 0 and zero_dur@ == 0.
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_duration_elapsed_ge_zero() {
    // elapsed spec: result@ >= 0
    let elapsed_assumption = ge(var("elapsed"), int(0));

    // zero_dur@ == 0
    let zero_dur_assumption = eq(var("zero_dur"), int(0));

    // ensures: elapsed@ >= zero_dur@ (the assert! check)
    let ens = ge(var("elapsed"), var("zero_dur"));
    let body = var("elapsed");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[elapsed_assumption, zero_dur_assumption], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "elapsed() >= zero_duration should verify: {result:?}"
    );
}

/// Instant checked_sub with zero: checked_sub(zero_dur).unwrap() == instant.
///
/// Models the instant.rs assertion: `instant.checked_sub(zero_dur).unwrap() == instant`
/// Uses CHECKED_SUB: `Some(v) => v@ == self@ - rhs@ && self@ >= rhs@`
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_instant_checked_sub_zero() {
    // instant@ >= 0
    let now_assumption = ge(var("instant"), int(0));

    // zero_dur@ == 0
    let zero_dur_assumption = eq(var("zero_dur"), int(0));

    // CHECKED_SUB match arm: when result == Some(v),
    //   v@ == self@ - rhs@ && self@ >= rhs@
    // With rhs = zero_dur (== 0), this gives v@ == instant@ - 0 == instant@
    // and instant@ >= 0 (which holds from now_assumption).
    //
    // The .unwrap() gives us v directly.
    let checked_sub_assumption = and(
        eq(var("unwrapped"), sub(var("instant"), var("zero_dur"))),
        ge(var("instant"), var("zero_dur")),
    );

    // ensures: unwrapped@ == instant@
    let ens = eq(var("unwrapped"), var("instant"));
    let body = var("unwrapped");

    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[now_assumption, zero_dur_assumption, checked_sub_assumption],
            &[ens],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "instant.checked_sub(zero).unwrap() == instant should verify: {result:?}"
    );
}
