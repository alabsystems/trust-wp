// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Chained capacity operations preserve Vec contents.
///
/// Models vector/09_capacity.rs pattern:
///   v.reserve(100);       // ensures: (^self)@ == self@
///   v.shrink_to_fit();    // ensures: (^self)@ == self@
/// After both, v contents are unchanged.
///
/// At ay level: reserve gives v1_len == v0_len, shrink gives v2_len == v1_len,
/// so v2_len == v0_len (transitivity).
///
/// Part of #1075
#[test]
#[timeout(30000)]
fn test_verify_chained_capacity_ops_preserve_len() {
    // Initial Vec state
    let v0_len_ge_zero = ge(var("v0_len"), int(0));

    // reserve postcondition: v1_len == v0_len
    let reserve_assumption = eq(var("v1_len"), var("v0_len"));

    // shrink_to_fit postcondition: v2_len == v1_len
    let shrink_assumption = eq(var("v2_len"), var("v1_len"));

    // ensures: v2_len == v0_len (len preserved across both operations)
    let ens = eq(var("v2_len"), var("v0_len"));

    let body = var("v2_len");

    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[v0_len_ge_zero, reserve_assumption, shrink_assumption],
            &[ens],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Chained capacity ops should preserve len: {result:?}"
    );
}
