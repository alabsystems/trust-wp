// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `old()` is not allowed in `#[requires]`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_wp::requires;

// ERROR: `old()` can only be used in #[ensures] postconditions
#[requires(old(x) > 0)]
fn bad_old_in_requires(x: i32) -> i32 {
    x
}

fn main() {}
