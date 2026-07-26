// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture: proof_assert! should verify when assertion follows from preconditions.

use trust_wp::{proof_assert, requires};

/// Function with a proof assertion that should verify.
///
/// The precondition `x > 0` implies the assertion `x >= 0`.
#[requires(x > 0)]
fn positive_implies_non_negative(x: i32) {
    // This should verify: x > 0 => x >= 0
    proof_assert!(x >= 0);
}

/// Function with a proof assertion on boolean expressions.
///
/// The precondition `a && b` implies the assertion `a`.
#[requires(a && b)]
fn and_implies_left(a: bool, b: bool) {
    // This should verify: (a && b) => a
    proof_assert!(a);
    let _ = b; // Suppress unused variable warning
}

/// Function with arithmetic proof assertion.
///
/// The precondition `x >= 0 && y >= 0` implies `x + y >= 0`.
#[requires(x >= 0)]
#[requires(y >= 0)]
fn sum_is_non_negative(x: i32, y: i32) {
    // This should verify: (x >= 0 && y >= 0) => (x + y >= 0)
    proof_assert!(x + y >= 0);
}

fn main() {
    positive_implies_non_negative(5);
    and_implies_left(true, true);
    sum_is_non_negative(1, 2);
}
