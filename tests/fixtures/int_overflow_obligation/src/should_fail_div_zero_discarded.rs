// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `a / b` whose QUOTIENT IS DISCARDED still divides by zero when b = 0.
//! Creusot: `UInt32.div` precondition `t'int b <> 0`.
//!
//! The twin of `should_fail_div_zero` that isolates the DRIVER-side lane.
//! When the quotient reaches the goal, trust-wp-ay's encoder-side divisor
//! obligation (`verify/postcondition.rs::divisor_known_nonzero_under_requires`)
//! refutes the contract on its own, so `should_fail_div_zero` stays RED even
//! if the MIR `Assert(DivisionByZero)` stopped owing anything. Here nothing
//! but that assert's own obligation can reject the program: a build whose
//! `build_arithmetic_panic_obligation` DivisionByZero arm yields `true`
//! ACCEPTS this fixture.

use trust_wp::ensures;

#[ensures(true)]
pub fn quot0_discarded(a: u32, b: u32) {
    let _z = a / b;
}

fn main() {}
