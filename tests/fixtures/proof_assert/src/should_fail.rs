// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture: proof_assert! should fail when assertion doesn't follow from preconditions.

use trust_wp::{proof_assert, requires};

/// Function with a proof assertion that should fail.
///
/// The precondition `x >= 0` does NOT imply `x > 0` (x could be 0).
#[requires(x >= 0)]
fn non_negative_does_not_imply_positive(x: i32) {
    // This should FAIL: x >= 0 does not imply x > 0 (counterexample: x = 0)
    proof_assert!(x > 0);
}

fn main() {
    non_negative_does_not_imply_positive(0);
}
