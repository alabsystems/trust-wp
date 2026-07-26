// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `result` cannot be used in #[variant]
//!
//! Variants are termination measures that must decrease. They're evaluated
//! during loop/recursion execution, before any result exists.
//!
//! Issue: #212 (bug fix), #213 (test)

use trust_wp_macros::variant;

// ERROR: `result` can only be used in #[ensures] postconditions
#[variant(result - 1)]
fn bad_result_variant(n: i32) -> i32 {
    if n <= 0 { 0 } else { bad_result_variant(n - 1) + 1 }
}

fn main() {}
