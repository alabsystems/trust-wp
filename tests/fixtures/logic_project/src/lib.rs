// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function fixture for cargo-trust-wp integration tests.
//!
//! Exercises logic functions used in contracts. Includes both verifying and
//! failing examples.

use trust_wp::{ensures, law, logic, requires};

#[logic]
fn add_one(x: i32) -> i32 {
    x + 1
}

#[logic(open)]
fn add_one_open(x: i32) -> i32 {
    x + 1
}

#[logic]
fn double(x: i32) -> i32 {
    x + x
}

#[ensures(result == add_one_open(x))]
pub fn add_one_runtime(x: i32) -> i32 {
    x + 1
}

#[ensures(result == double(x))]
pub fn double_runtime(x: i32) -> i32 {
    x + x
}

#[requires(x >= 0)]
#[ensures(result > add_one_open(x))]
pub fn add_one_buggy(x: i32) -> i32 {
    x + 1
}

// =============================================================================
// #[law] tests — axiom-visible logic functions (#716)
// =============================================================================

/// A law function: body is visible to the solver (equivalent to #[logic(open)]).
/// The defining axiom `forall x. triple(x) = x + x + x` is emitted.
#[law]
fn triple(x: i32) -> i32 {
    x + x + x
}

/// Uses the `triple` law function in a postcondition.
/// Should VERIFY because `#[law]` emits the defining axiom (Open mode).
#[ensures(result == triple(x))]
pub fn triple_runtime(x: i32) -> i32 {
    x + x + x
}

pub mod cross_module {
    use trust_wp::ensures;

    /// Cross-module use of bare `#[logic]` must stay opaque in Default mode.
    /// If `add_one` were incorrectly opened here, this would verify.
    #[ensures(result == super::add_one(x))]
    pub fn cross_module_default_opaque(x: i32) -> i32 {
        x + 1
    }
}
