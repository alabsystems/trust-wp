// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `old()` cannot be used in proof_assert!
//!
//! The `old()` expression captures a value at function entry, but proof_assert!
//! runs at a specific program point. Use snapshot! to capture values instead.

use trust_wp_macros::proof_assert;

fn bad_proof_assert(x: &mut i32) {
    *x += 1;
    // ERROR: `old()` can only be used in #[ensures] postconditions
    // Use snapshot! instead to capture values at specific points
    proof_assert!(old(*x) == 0);
}

fn main() {}
