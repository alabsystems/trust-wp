// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Vec push length increment: after push, len increases by 1.
///
/// Models the core postcondition from Vec::PUSH spec:
///   ensures: (^self)@.len() == self@.len() + 1
///
/// At ay level, this means: given push_len == old_len + 1,
/// the postcondition push_len == old_len + 1 holds.
///
/// Part of #1075
#[test]
#[timeout(30000)]
fn test_verify_vec_push_len_increment() {
    // self@.len() before push
    let old_len_assumption = ge(var("old_len"), int(0));

    // Call-site assumption from push spec:
    //   push_len == old_len + 1
    let push_assumption = eq(var("push_len"), add(var("old_len"), int(1)));

    // ensures: push_len == old_len + 1
    let ens = eq(var("push_len"), add(var("old_len"), int(1)));

    let body = var("push_len");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[old_len_assumption, push_assumption], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Vec push length increment should verify: {result:?}"
    );
}
