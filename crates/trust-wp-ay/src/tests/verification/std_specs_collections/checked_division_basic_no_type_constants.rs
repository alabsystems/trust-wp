// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Checked division encoding: u8 division without type_constants.
///
/// Same as above, but the ensures also checks that Self::MIN and Self::MAX
/// don't need to be involved for checked_div (which doesn't reference them).
/// This verifies that the checked_div spec path doesn't introduce free
/// Self::MIN/Self::MAX variables.
///
/// Part of #967
#[test]
#[timeout(30000)]
fn test_verify_checked_div_u8_no_self_min_max_needed() {
    // requires: b != 0
    let req = ne(var("b"), int(0));

    // Call-site assumption from checked_div spec (no Self::MIN/MAX):
    let cd_assumption = implies(
        ne(var("b"), int(0)),
        eq(var("cd_result"), div(var("a"), var("b"))),
    );

    // ensures: cd_result == a / b
    let ens = eq(var("cd_result"), div(var("a"), var("b")));

    let body = var("cd_result");

    // No type_constants — this should still verify because checked_div
    // doesn't reference Self::MIN or Self::MAX.
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, cd_assumption], &[ens]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "checked_div should verify without type_constants: {result:?}"
    );
}
