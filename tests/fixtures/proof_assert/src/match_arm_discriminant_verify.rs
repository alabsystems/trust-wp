// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! proof_assert inside a `match` arm should see the arm discriminant guard.
//!
//! For `match b { true => ... }`, the assertion `proof_assert!(b)` is only
//! valid in the `true` arm. Extraction must carry that branch condition to the
//! proof_assert program point.

use trust_wp::proof_assert;

fn match_arm_discriminant_verify(b: bool) -> bool {
    match b {
        true => {
            proof_assert!(b);
            b
        }
        false => false,
    }
}

fn main() {
    let _ = match_arm_discriminant_verify(true);
}
