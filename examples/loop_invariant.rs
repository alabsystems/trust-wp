// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop invariant example demonstrating verification with loops.
//!
//! STATUS: Fully implemented. See `verify_loop_invariant` in trust-wp-ay.
//!
//! The implementation supports:
//! - Loop detection via back-edge analysis
//! - `#[invariant]` attribute parsing
//! - Loop structure reporting
//! - **Initialization check**: Invariant holds at loop entry (requires => inv)
//! - **Preservation check**: Invariant maintained by loop body (inv && cond => inv')
//! - **Postcondition check**: Invariant implies postcondition when loop exits
//! - **Variant checks** (optional): Termination via decreasing expressions

use trust_wp::{ensures, invariant, requires};

/// Sum of first n natural numbers.
///
/// Invariant: `sum == i * (i - 1) / 2`
/// At each iteration, sum holds the sum of 0..i.
///
/// Postcondition: `result == n * (n + 1) / 2`
#[requires(n >= 0)]
#[ensures(result >= 0)]
#[invariant(sum >= 0)]
fn sum_first_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i <= n {
        sum += i;
        i += 1;
    }
    sum
}

/// Count down from n to 0.
///
/// This demonstrates a simple decrementing loop.
/// Invariant: `count >= 0` (always non-negative)
#[requires(n >= 0)]
#[ensures(result == 0)]
#[invariant(count >= 0)]
fn count_down(n: i32) -> i32 {
    let mut count = n;
    while count > 0 {
        count -= 1;
    }
    count
}

/// Factorial function (n!).
///
/// Note: This will overflow for n > 12 with i32.
/// Invariant: `acc >= 1` (factorial is always positive)
#[requires(n >= 0 && n <= 12)]
#[ensures(result >= 1)]
#[invariant(acc >= 1)]
fn factorial(n: i32) -> i32 {
    let mut acc = 1;
    let mut i = 1;
    while i <= n {
        acc *= i;
        i += 1;
    }
    acc
}

fn main() {
    // Sum of 0..=10 = 55
    let sum = sum_first_n(10);
    println!("sum_first_n(10) = {}", sum);
    assert_eq!(sum, 55);

    // Count down from 5 to 0
    let zero = count_down(5);
    println!("count_down(5) = {}", zero);
    assert_eq!(zero, 0);

    // 5! = 120
    let fact = factorial(5);
    println!("factorial(5) = {}", fact);
    assert_eq!(fact, 120);
}
