// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `old()` cannot be used in #[requires]
//!
//! The `old()` function captures a value at function entry, which only makes
//! sense in postconditions (#[ensures]) where we compare with post-state.
//!
//! Issue: #212 (bug fix), #213 (test)

use trust_wp_macros::requires;

// ERROR: `old()` can only be used in #[ensures] postconditions
#[requires(old(x) > 0)]
fn bad_old_requires(x: i32) -> i32 {
    x + 1
}

fn main() {}
