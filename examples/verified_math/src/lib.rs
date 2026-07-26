// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verified Math Functions
//!
//! This library demonstrates trust-wp contract verification with simple
//! mathematical functions. Each function has preconditions (#[requires])
//! and postconditions (#[ensures]) that trust-wp proves correct.
//!
//! ## Verifying this Library
//!
//! ```bash
//! # From trust-wp root directory:
//! ./scripts/run-trust-wp-rustc.sh examples/verified_math/src/lib.rs --crate-type=lib -- --force
//! ```

use trust_wp::{ensures, requires};

// ============================================================================
// BASIC ARITHMETIC
// ============================================================================

/// Safely increment a value, avoiding overflow.
///
/// # Contract
/// - **Precondition**: `x` must be less than `i32::MAX` to avoid overflow
/// - **Postcondition**: The result equals `x + 1`
#[requires(x < 2147483647)]
#[ensures(result == x + 1)]
pub fn safe_increment(x: i32) -> i32 {
    x + 1
}

/// Double a value with bounded input.
///
/// # Contract
/// - **Precondition**: Input must be in range [-1000, 1000] to avoid overflow
/// - **Postcondition**: The result equals `x * 2`
#[requires(x >= -1000 && x <= 1000)]
#[ensures(result == x * 2)]
pub fn double(x: i32) -> i32 {
    x * 2
}

/// Compute absolute value (safe for all inputs except MIN).
///
/// # Contract
/// - **Precondition**: `x` must not be `i32::MIN` (negation would overflow)
/// - **Postcondition**: The result is non-negative
#[requires(x > -2147483648)]
#[ensures(result >= 0)]
pub fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

// ============================================================================
// COMPARISON FUNCTIONS
// ============================================================================

/// Check if a value is positive.
///
/// # Contract
/// - **Postcondition**: Result is true iff input is greater than zero
#[ensures(result == (x > 0))]
pub fn is_positive(x: i32) -> bool {
    x > 0
}

/// Return zero (identity under addition).
///
/// # Contract
/// - **Postcondition**: Adding result to any value x gives x back
#[ensures(result == 0)]
pub fn zero() -> i32 {
    0
}

/// Negate a boolean.
///
/// # Contract
/// - **Postcondition**: Result is opposite of input
#[ensures(result == !b)]
pub fn negate(b: bool) -> bool {
    !b
}

// ============================================================================
// TESTS (for runtime verification that code matches contracts)
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_increment() {
        assert_eq!(safe_increment(0), 1);
        assert_eq!(safe_increment(100), 101);
        assert_eq!(safe_increment(-100), -99);
    }

    #[test]
    fn test_double() {
        assert_eq!(double(0), 0);
        assert_eq!(double(5), 10);
        assert_eq!(double(-5), -10);
    }

    #[test]
    fn test_abs() {
        assert_eq!(abs(0), 0);
        assert_eq!(abs(42), 42);
        assert_eq!(abs(-42), 42);
    }

    #[test]
    fn test_is_positive() {
        assert!(is_positive(1));
        assert!(!is_positive(0));
        assert!(!is_positive(-1));
    }

    #[test]
    fn test_zero() {
        assert_eq!(zero(), 0);
    }

    #[test]
    fn test_negate() {
        assert!(!negate(true));
        assert!(negate(false));
    }
}
