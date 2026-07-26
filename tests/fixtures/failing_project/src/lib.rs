// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Failing project fixture for cargo-trust-wp integration tests.
//!
//! Contracts here are intentionally incorrect and should fail verification.

use trust_wp::{ensures, requires};

/// Buggy increment that doesn't satisfy contract when x == 0.
///
/// The postcondition says result > x, but when x == 0, result == 1 > 0 is true.
/// However, the precondition says x > 0, so x == 0 is invalid input.
/// Let's make a genuinely buggy function:
#[requires(x >= 0)]  // allows x == 0
#[ensures(result > x)]  // claims result > x
pub fn buggy_increment(x: i32) -> i32 {
    // Bug: when x is i32::MAX, this wraps around!
    // Also, returning x violates result > x for any x
    x  // Should be x + 1
}

/// Another buggy function - claims abs is always positive but doesn't handle MIN.
#[ensures(result > 0)]  // Should be >= 0
pub fn buggy_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
    // Bug: result is 0 when x == 0, but contract says > 0
}
