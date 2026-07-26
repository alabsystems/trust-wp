// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression fixture for #927:
//! call obligations nested under both ITE branches must be enforced as goals,
//! not asserted as assumptions.
//!
//! If branch-local obligations are treated as assumptions, `x == 0` is silently
//! eliminated by the else-branch obligation and this assertion may verify
//! vacuously. Correct behavior is failure, because `x < 0` is not guaranteed in
//! the else branch (`x <= 0`).

use trust_wp::{ensures, proof_assert, requires};

#[requires(x > 0)]
#[ensures(result > 0)]
fn id_pos(x: i32) -> i32 {
    x
}

#[requires(x < 0)]
#[ensures(result < 0)]
fn id_neg(x: i32) -> i32 {
    x
}

fn multibranch_obligation_unsound(x: i32) {
    if x > 0 {
        let _ = id_pos(x);
    } else {
        let _ = id_neg(x);
    }
    // This must fail: else branch only gives x <= 0, not x < 0.
    // The id_neg precondition remains a proof obligation for x == 0.
    proof_assert!(x != 0);
}

fn main() {
    multibranch_obligation_unsound(0);
}
