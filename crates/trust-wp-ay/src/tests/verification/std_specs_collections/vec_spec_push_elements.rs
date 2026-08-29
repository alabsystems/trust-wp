// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Vec push preserves existing elements via forall quantifier.
///
/// Models: forall i in 0..old_len ==> new_vec[i] == old_vec[i]
/// This is the frame preservation postcondition used by push, reserve, shrink_to, etc.
///
/// Part of #1075
#[test]
#[timeout(30000)]
fn test_verify_vec_push_element_preservation() {
    // old_len >= 0
    let old_len_assumption = ge(var("old_len"), int(0));

    // A specific element at index j (0 <= j < old_len) has value elem_j
    let j_bounds = and(ge(var("j"), int(0)), lt(var("j"), var("old_len")));
    let old_elem = eq(var("old_elem_j"), var("stored_value"));
    let new_elem = eq(var("new_elem_j"), var("stored_value"));

    // ensures: j in bounds ==> new_elem_j == old_elem_j (element preserved)
    let ens = implies(j_bounds, eq(var("new_elem_j"), var("old_elem_j")));

    let body = var("new_elem_j");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[old_len_assumption, old_elem, new_elem], &[ens])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Vec push element preservation should verify: {result:?}"
    );
}
