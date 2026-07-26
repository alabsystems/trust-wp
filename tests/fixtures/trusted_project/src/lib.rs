// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture for trusted function verification.

use trust_wp::{ensures, requires, trusted};

/// A trusted function - postcondition is assumed, body is not verified.
/// The postcondition is WRONG (returns 42, not > 100) but verification should skip.
#[trusted]
#[ensures(result > 100)]
pub fn trusted_external() -> i32 {
    42  // This would FAIL verification if not trusted
}

/// A regular function that gets verified.
/// Precondition ensures no overflow and result > 0.
#[requires(x >= 0)]
#[requires(x < i32::MAX)]
#[ensures(result > 0)]
pub fn verified_increment(x: i32) -> i32 {
    x + 1
}
