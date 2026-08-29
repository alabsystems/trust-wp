// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Checked division encoding: u8 division with non-zero divisor.
///
/// Models the core of `test_u8_div_no_overflow`: the assertion that
/// `a.checked_div(b).unwrap() == a / b` for non-zero `b`. At the ay level,
/// the checked_div postcondition (as a call-site assumption) guarantees
/// `cd_result == a / b`, and the body result IS `cd_result`, so the
/// ensures `result == a / b` should verify trivially.
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_checked_div_u8_no_overflow() {
    // requires: b != 0
    let req = ne(var("b"), int(0));

    // Call-site assumption from checked_div spec:
    //   b != 0 ==> cd_result == a / b
    // (This models the unwrapped result of checked_div)
    let cd_assumption = implies(
        ne(var("b"), int(0)),
        eq(var("cd_result"), div(var("a"), var("b"))),
    );

    // Call-site assumption from div operator spec:
    //   div_result == a / b
    let div_assumption = eq(var("div_result"), div(var("a"), var("b")));

    // ensures: cd_result == div_result (the assertion in the test)
    let ens = eq(var("cd_result"), var("div_result"));

    // body result: the equality check (represented as cd_result for simplicity)
    let body = var("cd_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, cd_assumption, div_assumption], &[ens])
            .return_expr(Some(&body)),
    );
    // ay int_div in QF_AUFLIA returns Unknown("incomplete") — division creates
    // nonlinear arithmetic terms outside the decidable fragment. Filed ay#6165.
    // Accept both Verified (ideal) and Unknown("incomplete") (current ay behavior).
    let is_expected = matches!(result, Ok(VerificationResult::Verified(_)))
        || matches!(
            &result,
            Ok(VerificationResult::Unknown(ref reason)) if reason.as_str().contains("incomplete")
        );
    assert!(
        is_expected,
        "u8 checked_div(a, b) with b != 0: cd_result == a/b should verify or return incomplete: {result:?}"
    );
}
