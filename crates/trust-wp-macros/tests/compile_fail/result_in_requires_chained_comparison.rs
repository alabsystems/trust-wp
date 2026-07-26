// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: `result` cannot be used in #[requires]
//! with non-Rust chained comparison syntax.
//!
//! This forces the proc-macro fallback parser path (`a < b < c`) and
//! verifies special-form validation is still enforced there.
//!
//! Issue: #358 (fallback validation coverage)

use trust_wp_macros::requires;

// ERROR: `result` can only be used in #[ensures] postconditions
#[requires(0 < result < 10)]
fn bad_requires_chain(x: i32) -> i32 {
    x
}

fn main() {}
