//@ expect: verify
//@ mechanism: TRUE twin of quantifier_binder_128_bit_machine_int_range_overflows.rs: each claim holds over
//@ mechanism: exactly the 128-bit type's values, and needs the binder's range to hold (an unbounded
//@ mechanism: binder refutes it).
//@ teeth: over-refusal control. MEASURED in the debug build: the contract macro panics on every clause
//@ teeth: here and the crate does not compile. With D-211: each function verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(forall<x: u128> 0 <= x@)]
pub fn u128_low() {}

#[ensures(forall<x: u128> x@ < 4294967296 * 4294967296 * 4294967296 * 4294967296)]
pub fn u128_high() {}

#[ensures(forall<x: i128> -(2147483648 * 4294967296 * 4294967296 * 4294967296) <= x@)]
pub fn i128_low() {}

#[ensures(forall<x: i128> x@ < 2147483648 * 4294967296 * 4294967296 * 4294967296)]
pub fn i128_high() {}
