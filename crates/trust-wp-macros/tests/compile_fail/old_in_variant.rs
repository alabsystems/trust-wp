// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `old()` cannot be used in #[variant]
//!
//! Variants are termination measures evaluated at each loop iteration.
//! The `old()` form captures function entry state, not loop iteration state.
//!
//! Issue: #212 (bug fix), #213 (test)

use trust_wp_macros::variant;

// ERROR: `old()` can only be used in #[ensures] postconditions
#[variant(old(n) - i)]
fn bad_old_variant(n: i32) -> i32 {
    let mut i = 0;
    while i < n { i += 1; }
    i
}

fn main() {}
