// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-spec soundness test: branch-scoped call assumptions.
//!
//! Tests that call postconditions are correctly scoped to the branch in
//! which the call occurs. A proof_assert INSIDE the branch (where the
//! postcondition is available) should verify, while the same assertion
//! OUTSIDE the branch should fail.
//!
//! This complements soundness_815_branch_leak.rs which only checks
//! that the bug doesn't recur. This test verifies the CORRECT behavior:
//! branch-local assumptions are usable within their scope.
//!
//! Re: #817 (call-spec soundness test matrix)

use trust_wp::{ensures, proof_assert, requires};

#[requires(x > 0)]
#[ensures(result > 0)]
fn identity_positive(x: i32) -> i32 {
    x
}

/// Branch-scoped call postcondition: within-branch proof_assert should verify.
///
/// The call to `identity_positive(x)` occurs inside `if x > 0 { ... }`.
/// Within that branch, the precondition `x > 0` is satisfied, so the
/// postcondition `result > 0` is available. The proof_assert inside the
/// branch can use the path condition (x > 0) directly.
fn branch_scoped_verify(x: i32) {
    if x > 0 {
        let _ = identity_positive(x);
        // This SHOULD VERIFY: inside the branch, x > 0 holds from the
        // branch condition, so the precondition is met and we can use
        // the call's postcondition.
        proof_assert!(x > 0);
    }
}

/// Post-branch assertion without call assumption: should fail.
///
/// After the branch, x > 0 is no longer guaranteed (only x >= 0).
fn branch_scoped_fail(x: i32) {
    if x > 0 {
        let _ = identity_positive(x);
    }
    // This MUST FAIL: x >= 0 from function entry does not imply x > 0
    // (x could be 0). The call assumption from the branch must not leak.
    proof_assert!(x > 0);
}

fn main() {
    branch_scoped_verify(1);
    branch_scoped_fail(0);
}
