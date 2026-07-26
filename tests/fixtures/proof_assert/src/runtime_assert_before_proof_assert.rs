// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests that MIR body extraction handles runtime assert!() between
//! function calls and proof_assert!().
//!
//! Pattern from Creusot duration.rs:
//!   let x = some_call();
//!   assert!(condition);  // runtime assert
//!   proof_assert!(something);
//!
//! The runtime assert! macro generates a bool SwitchInt with a panic branch
//! in MIR. The extraction pipeline must traverse this without failing, since
//! cutoff-reachability filtering drops the unreachable panic arm.
//!
//! Re: #746

use trust_wp::{ensures, proof_assert, requires};

#[requires(x > 0)]
#[ensures(result > 0)]
fn identity_positive(x: i32) -> i32 {
    x
}

/// Simple case: opaque call, then runtime assert, then proof_assert.
fn assert_between_call_and_proof_assert() {
    let y = identity_positive(1);
    assert!(y > 0); // This generates SwitchInt in MIR
    proof_assert!(y > 0);
}

/// Simpler case: just a let-binding, runtime assert, then proof_assert.
fn assert_after_let_binding() {
    let x = 42;
    assert!(x > 0);
    proof_assert!(x > 0);
}

fn main() {
    assert_between_call_and_proof_assert();
    assert_after_let_binding();
}
