// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `result` cannot be used in #[requires]
//!
//! The `result` keyword refers to the function's return value and is only
//! valid in postconditions (#[ensures]), not preconditions (#[requires]).
//!
//! Issue: #212 (bug fix), #213 (test)

use trust_wp_macros::requires;

// ERROR: `result` can only be used in #[ensures] postconditions
#[requires(result > 0)]
fn bad_requires(x: i32) -> i32 {
    x
}

fn main() {}
