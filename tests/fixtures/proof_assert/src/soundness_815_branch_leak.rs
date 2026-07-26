// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression fixture for #815: proof_assert Phase 2 soundness bugs.
//!
//! These functions SHOULD FAIL verification because their proof_assert
//! assertions do not follow from the available assumptions in scope.
//! If they verify, it means call-site assumptions are leaking from
//! branches or call preconditions are not being enforced.

use trust_wp::{ensures, proof_assert, requires};

/// #815 Problem A: Branch-local call assumption leaks globally.
///
/// The call `id_pos(x)` with postcondition `result > 0` occurs inside
/// `if x > 0 { ... }`, but the postcondition leaks to the global scope.
/// The assertion `proof_assert!(x > 0)` should FAIL because `x` could be
/// any value (no precondition on this function).
#[requires(x > 0)]
#[ensures(result > 0)]
fn id_pos(x: i32) -> i32 {
    x
}

fn branch_unsound(x: i32) {
    if x > 0 {
        let _ = id_pos(x);
    }
    // This MUST fail: x > 0 only holds inside the branch, not here.
    proof_assert!(x > 0);
}

/// #815 Problem B: Callee precondition not enforced.
///
/// `id_pos(x)` requires `x > 0`, but this function has no precondition
/// that guarantees it. The postcondition `result > 0` should NOT be
/// usable as an assumption unless the precondition `x > 0` is proved.
fn precondition_unsound(x: i32) {
    let _ = id_pos(x); // requires(x > 0) may not hold!
    // This MUST fail: we used the postcondition without proving the precondition.
    proof_assert!(x > 0);
}

fn main() {
    branch_unsound(0);
    precondition_unsound(0);
}
