// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Instant ordering: instant + positive_duration > instant.
///
/// Models: `proof_assert!(instant@ < greater_instant@)` after
/// `let greater_instant = instant + three_seconds` where three_seconds@ == 3.
/// Uses Add<Duration> spec: `result@ == self@ + rhs@`
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_instant_add_positive_ordering() {
    // instant@ >= 0
    let now_assumption = ge(var("instant"), int(0));

    // three_seconds@ == 3
    let dur_assumption = eq(var("three_seconds"), int(3));

    // greater_instant@ == instant@ + three_seconds@
    let add_assumption = eq(
        var("greater_instant"),
        add(var("instant"), var("three_seconds")),
    );

    // ensures: instant@ < greater_instant@
    let ens = lt(var("instant"), var("greater_instant"));
    let body = var("greater_instant");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[now_assumption, dur_assumption, add_assumption], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "instant@ < (instant + 3_seconds)@ should verify: {result:?}"
    );
}

/// Instant ordering with view variables: instant@ < greater_instant@.
///
/// Models the proof_assert pattern from Creusot compat instant.rs where
/// ghost context binds `instant == call_1` (struct level) and the assertion
/// uses view variables `instant@` and `greater_instant@`.
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_instant_add_positive_ordering_with_view() {
    // Ghost context: instant == call_1 (struct-level binding)
    let ghost_instant_binding = eq(var("instant"), var("call_1"));

    // Ghost context: greater_instant@ == call_1@ + 3 * 1_000_000_000
    let ghost_greater = eq(
        view(var("greater_instant")),
        add(view(var("call_1")), mul(int(3), int(1_000_000_000))),
    );

    // Ghost context: three_seconds@ == 3 * 1_000_000_000
    let ghost_three = eq(view(var("three_seconds")), mul(int(3), int(1_000_000_000)));

    // assumed fact: call_1@ > 0
    let now_assumption = gt(view(var("call_1")), int(0));

    // ensures: instant@ < greater_instant@
    let ens = lt(view(var("instant")), view(var("greater_instant")));

    let body = var("instant");

    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[
                ghost_instant_binding,
                ghost_greater,
                ghost_three,
                now_assumption,
            ],
            &[ens],
        )
        .return_expr(Some(&body))
        .ghost_context(Some(&[
            eq(var("instant"), var("call_1")),
            eq(
                view(var("greater_instant")),
                add(view(var("call_1")), mul(int(3), int(1_000_000_000))),
            ),
        ])),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "instant@ < greater_instant@ with view variables should verify: {result:?}"
    );
}

/// Instant subtraction ordering: instant - positive_duration < instant.
///
/// Models: `proof_assert!(instant@ > lesser_instant@)` after
/// `let lesser_instant = instant - three_seconds`.
/// Uses SUB_COMBINED spec clause 1: `self@ >= rhs@ ==> result@ == self@ - rhs@`
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_instant_sub_positive_ordering() {
    // instant@ >= 0, and instant@ >= 3 to avoid saturation
    let now_assumption = ge(var("instant"), int(3));

    // three_seconds@ == 3
    let dur_assumption = eq(var("three_seconds"), int(3));

    // SUB_COMBINED clause 1: self@ >= rhs@ ==> result@ == self@ - rhs@
    let sub_clause1 = implies(
        ge(var("instant"), var("three_seconds")),
        eq(
            var("lesser_instant"),
            sub(var("instant"), var("three_seconds")),
        ),
    );

    // ensures: instant@ > lesser_instant@
    let ens = gt(var("instant"), var("lesser_instant"));
    let body = var("lesser_instant");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[now_assumption, dur_assumption, sub_clause1], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "instant@ > (instant - 3_seconds)@ should verify: {result:?}"
    );
}
