// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function fixture for cargo-trust-wp integration tests.
//!
//! Exercises logic functions used in contracts. Includes both verifying and
//! failing examples. The logic functions compute over `Int` views: on `i32`
//! itself a logic `+` is the oracle's wrapping add (D-232).

use trust_wp::{ensures, law, logic, pearlite, requires, Int};

#[logic]
fn add_one(x: i32) -> Int {
    pearlite! { x@ + 1 }
}

#[logic(open)]
fn add_one_open(x: i32) -> Int {
    pearlite! { x@ + 1 }
}

#[logic]
fn double(x: i32) -> Int {
    pearlite! { x@ + x@ }
}

/// `x < i32::MAX` is the tightest bound that keeps `x + 1` from overflowing.
#[requires(x < i32::MAX)]
#[ensures(result@ == add_one_open(x))]
pub fn add_one_runtime(x: i32) -> i32 {
    x + 1
}

#[ensures(result@ == double(x))]
pub fn double_runtime(x: i32) -> i32 {
    x + x
}

#[requires(x >= 0)]
#[ensures(result@ > add_one_open(x))]
pub fn add_one_buggy(x: i32) -> i32 {
    x + 1
}

// =============================================================================
// #[law] tests — axiom-visible logic functions (#716)
// =============================================================================

/// A law function: body is visible to the solver (equivalent to #[logic(open)]).
/// The defining axiom `forall x. triple(x) = x@ + x@ + x@` is emitted.
#[law]
fn triple(x: i32) -> Int {
    pearlite! { x@ + x@ + x@ }
}

/// Uses the `triple` law function in a postcondition.
/// Should VERIFY because `#[law]` emits the defining axiom (Open mode).
///
/// The bound is exactly the set of `x` for which `x + x + x` stays in `i32`:
/// `3 * 715_827_882 == 2_147_483_646 <= i32::MAX` and
/// `3 * -715_827_882 == -2_147_483_646 >= i32::MIN`, while one more step
/// either way leaves the range. (`x + x` alone tolerates a wider `x`, so the
/// three-term bound is the binding one.)
#[requires(x >= -715_827_882 && x <= 715_827_882)]
#[ensures(result@ == triple(x))]
pub fn triple_runtime(x: i32) -> i32 {
    x + x + x
}

pub mod cross_module {
    use trust_wp::ensures;

    /// Cross-module use of bare `#[logic]` must stay opaque in Default mode.
    /// If `add_one` were incorrectly opened here, this would verify.
    #[ensures(result@ == super::add_one(x))]
    pub fn cross_module_default_opaque(x: i32) -> i32 {
        x + 1
    }
}
