// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `result` cannot be used in proof_assert!
//!
//! The `result` keyword refers to the function's return value and is only
//! valid in postconditions (#[ensures]). proof_assert! is checked at a specific
//! program point where the result may not be determined yet.

use trust_wp_macros::proof_assert;

fn bad_proof_assert(x: i32) -> i32 {
    // ERROR: `result` can only be used in #[ensures] postconditions
    proof_assert!(result > 0);
    x
}

fn main() {}
