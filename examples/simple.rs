// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Simple example for testing trust-wp MIR extraction
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// This file demonstrates a simple function with contracts.
// It can be compiled with: ./scripts/run-trust-wp-rustc.sh examples/simple.rs -- --force
//
// Contracts use Creusot-compatible proc-macro syntax: #[requires(...)]
// The trust-wp driver extracts these during compilation.

use trust_wp::{ensures, requires};

/// A simple increment function with contracts.
///
/// The `#[requires]` and `#[ensures]` attributes specify the function's
/// contract using Creusot-compatible syntax.
#[requires(x > i32::MIN)]
#[ensures(result == x + 1)]
fn increment(x: i32) -> i32 {
    x + 1
}

/// An absolute value function.
///
/// Requires x > i32::MIN because negating MIN would overflow.
#[requires(x > i32::MIN)]
#[ensures(result >= 0)]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn main() {
    let y = increment(5);
    assert_eq!(y, 6);
    println!("increment(5) = {}", y);

    let z = abs(-42);
    assert_eq!(z, 42);
    println!("abs(-42) = {}", z);
}
