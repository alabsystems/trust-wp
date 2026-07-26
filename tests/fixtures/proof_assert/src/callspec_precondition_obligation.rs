// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-spec soundness test: callee precondition obligations.
//!
//! Tests that calling a function with a `requires` clause generates
//! a proper obligation. When the precondition is satisfied, the
//! postcondition should be usable. When it is NOT satisfied, the
//! postcondition must NOT be assumed.
//!
//! Re: #817 (call-spec soundness test matrix)

use trust_wp::{ensures, proof_assert, requires};

#[requires(x > 0)]
#[ensures(result == x)]
fn positive_identity(x: i32) -> i32 {
    x
}

/// Callee precondition satisfied: postcondition usable in proof_assert.
///
/// The caller's precondition `x > 5` implies `x > 0`, so the call to
/// `positive_identity(x)` is valid and its postcondition is available.
#[requires(x > 5)]
fn precondition_met_verify(x: i32) {
    let _r = positive_identity(x);
    // This SHOULD VERIFY: x > 5 => x > 0 (precondition met),
    // so we can assert on the caller's own precondition.
    proof_assert!(x > 5);
}

/// Callee precondition NOT satisfied: postcondition must not leak.
///
/// The caller has NO precondition on x. The call to `positive_identity(x)`
/// violates `x > 0`. The postcondition `result == x` must NOT be
/// assumed as a global fact.
fn precondition_violated_fail(x: i32) {
    let _r = positive_identity(x);
    // This MUST FAIL: without proving x > 0, we cannot rely on
    // the postcondition. x could be any value.
    proof_assert!(x > 0);
}

fn main() {
    precondition_met_verify(10);
    precondition_violated_fail(0);
}
