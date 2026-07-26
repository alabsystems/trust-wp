// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simple project fixture for cargo-trust-wp integration tests.
//!
//! All contracts here should verify successfully.

use trust_wp::{ensures, requires};

/// Increment a positive number.
///
/// # Contracts
/// - requires: x > 0
/// - ensures: result > x
#[requires(x > 0)]
#[ensures(result > x)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

/// Return the absolute value of a number.
///
/// # Contracts
/// - ensures: result >= 0
#[ensures(result >= 0)]
pub fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

/// Identity function - simplest possible contract.
#[ensures(result == x)]
pub fn identity(x: i32) -> i32 {
    x
}
