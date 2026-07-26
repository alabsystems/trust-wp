// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-spec soundness test: bool-returning functions in proof_assert path.
//!
//! Tests that functions returning bool with predicate-style ensures work
//! correctly in the proof_assert path — both verification and failure.
//! This extends soundness_816_bool_ice.rs which only checks for no crash.
//!
//! Re: #817 (call-spec soundness test matrix)

use trust_wp::{ensures, proof_assert, requires};

#[requires(flag)]
#[ensures(result == true)]
fn is_truthy(flag: bool) -> bool {
    flag
}

/// Bool-return call with satisfied precondition: should verify.
///
/// The precondition `flag == true` implies `flag` (the callee requires).
/// After the call, `result == true` should be usable.
#[requires(flag == true)]
fn bool_call_verify(flag: bool) {
    let _r = is_truthy(flag);
    // This SHOULD VERIFY: flag == true from precondition satisfies
    // the callee's requires(flag), and the assertion follows directly.
    proof_assert!(flag);
}

/// Bool-return call with unsatisfied precondition: should fail.
///
/// No precondition on `flag`, so calling `is_truthy(flag)` violates
/// `requires(flag)`. The postcondition must not leak.
fn bool_call_fail(flag: bool) {
    let _r = is_truthy(flag);
    // This MUST FAIL: flag is unconstrained; calling is_truthy(flag)
    // violated the precondition, so the postcondition is not available.
    proof_assert!(flag);
}

fn main() {
    bool_call_verify(true);
    bool_call_fail(false);
}
