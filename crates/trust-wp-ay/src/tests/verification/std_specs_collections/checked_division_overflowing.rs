// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Overflowing division encoding: u8 overflowing_div with non-zero divisor.
///
/// Models: overflowing_div returns (a/b, false) for u8 with non-zero divisor.
/// The ensures checks `result.0 == a / b && result.1 == false`.
///
/// This test verifies the tuple-based postcondition encoding works correctly
/// when type_constants are NOT needed (unsigned division never overflows).
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_overflowing_div_u8() {
    // requires: b != 0
    let req = ne(var("b"), int(0));

    // Call-site assumption from overflowing_div spec:
    //   result_0 == a / b  (the quotient)
    //   result_1 == false  (no overflow for unsigned)
    let ov_div_quotient = eq(var("result_0"), div(var("a"), var("b")));
    let ov_div_overflow = eq(var("result_1"), bool_expr(false));

    // ensures: result_0 == a / b && result_1 == false
    let ens = and(
        eq(var("result_0"), div(var("a"), var("b"))),
        eq(var("result_1"), bool_expr(false)),
    );

    // body: the tuple fields (result_0, result_1) are already set by call-site assumptions
    let body = var("result_0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, ov_div_quotient, ov_div_overflow], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "u8 overflowing_div should verify: quotient==a/b, overflow==false: {result:?}"
    );
}
