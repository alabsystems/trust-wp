// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Basic contract examples for trust-wp
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This file demonstrates the contract syntax supported by trust-wp.
//! Compile with: cargo build -p trust-wp-examples (once examples crate exists)
//! Or include trust-wp as a dependency in your project.

use trust_wp::{ensures, requires};

// ============================================================================
// PRECONDITIONS (#[requires])
// ============================================================================

/// Simple comparison precondition
#[requires(x > 0)]
pub fn positive_only(x: i32) -> i32 {
    x
}

/// Compound precondition with logical AND
#[requires(x >= 0 && x < 100)]
pub fn bounded_value(x: i32) -> i32 {
    x
}

/// Precondition with logical OR
#[requires(x == 0 || x == 1)]
pub fn binary_flag(x: i32) -> bool {
    x != 0
}

/// Precondition on method calls
#[requires(v.len() > 0)]
pub fn first_element(v: &[i32]) -> i32 {
    v[0]
}

/// Precondition on struct fields
pub struct Point {
    pub x: i32,
    pub y: i32,
}

#[requires(p.x >= 0 && p.y >= 0)]
pub fn first_quadrant(p: &Point) -> bool {
    let _ = p; // Contract uses p, function body demonstrates precondition satisfied
    true
}

// ============================================================================
// POSTCONDITIONS (#[ensures])
// ============================================================================

/// Simple postcondition using `result`
#[ensures(result > 0)]
pub fn always_positive() -> i32 {
    42
}

/// Postcondition relating result to input
#[ensures(result == x + 1)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

/// Postcondition with `old()` for pre-state capture
#[ensures(result == old(x) * 2)]
pub fn double(x: i32) -> i32 {
    x * 2
}

/// Postcondition with `old()` on method calls
#[ensures(result == old(v.len()) - 1)]
pub fn pop_and_return_new_len(v: &mut Vec<i32>) -> usize {
    v.pop();
    v.len()
}

// ============================================================================
// COMBINED CONTRACTS
// ============================================================================

/// Multiple contracts on the same function
#[requires(x > 0)]
#[ensures(result > x)]
pub fn double_positive(x: i32) -> i32 {
    x * 2
}

/// Implication pattern: P => Q encoded as !P || Q
/// This reads: "if x > 0, then result == x" (non-positive inputs return 0)
#[ensures(!(x > 0) || result == x)] // x > 0 implies result == x
#[ensures(!(x <= 0) || result == 0)] // x <= 0 implies result == 0
#[ensures(result >= 0)] // result is always non-negative
pub fn at_least_input(x: i32) -> i32 {
    if x > 0 {
        x
    } else {
        0
    }
}

// ============================================================================
// LOOP INVARIANTS (#[invariant])
// ============================================================================

// Note: Loop invariants require unstable Rust features (#![feature(stmt_expr_attributes)])
// to use `#[invariant]` on while/for loop expressions. See contract-syntax.md (repo root).
//
// Example syntax (requires nightly + feature flags):
// ```
// // Invariant: sum equals triangular number T(i) = i*(i+1)/2, which is 1+2+...+i
// #[trust_wp::invariant(sum == i * (i + 1) / 2 && i <= n)]
// while i < n {
//     i += 1;
//     sum += i;
// }
// ```

// ============================================================================
// LOGIC FUNCTIONS (#[logic])
// ============================================================================

/// Logic function - exists only in specifications
#[trust_wp::logic]
fn abs(x: i32) -> i32 {
    if x >= 0 {
        x
    } else {
        -x
    }
}

/// Using logic function in contract
#[ensures(result == abs(x))]
pub fn absolute_value(x: i32) -> i32 {
    if x >= 0 {
        x
    } else {
        -x
    }
}

/// Logic function for max of two values
#[trust_wp::logic]
fn max(a: i32, b: i32) -> i32 {
    if a >= b {
        a
    } else {
        b
    }
}

/// Using logic function in postcondition
#[ensures(result == max(a, b))]
pub fn maximum(a: i32, b: i32) -> i32 {
    if a >= b {
        a
    } else {
        b
    }
}

// ============================================================================
// MAIN (for testing compilation)
// ============================================================================

fn main() {
    // Test that all contracts compile and functions work
    assert_eq!(positive_only(5), 5);
    assert_eq!(bounded_value(50), 50);
    assert!(binary_flag(1));
    assert_eq!(first_element(&[1, 2, 3]), 1);
    assert!(first_quadrant(&Point { x: 1, y: 2 }));
    assert_eq!(always_positive(), 42);
    assert_eq!(increment(5), 6);
    assert_eq!(double(5), 10);

    let mut v = vec![1, 2, 3];
    assert_eq!(pop_and_return_new_len(&mut v), 2);

    assert_eq!(double_positive(5), 10);
    assert_eq!(double_positive(1), 2); // boundary: minimum valid input
    assert_eq!(at_least_input(5), 5);
    assert_eq!(at_least_input(-5), 0);
    assert_eq!(at_least_input(0), 0); // boundary: 0 is not > 0

    // Logic function examples
    assert_eq!(absolute_value(5), 5);
    assert_eq!(absolute_value(-5), 5);
    assert_eq!(absolute_value(0), 0); // boundary case
    assert_eq!(maximum(3, 7), 7);
    assert_eq!(maximum(10, 2), 10);
    assert_eq!(maximum(5, 5), 5); // equal values case

    println!("All contract examples compiled and ran successfully!");
}
