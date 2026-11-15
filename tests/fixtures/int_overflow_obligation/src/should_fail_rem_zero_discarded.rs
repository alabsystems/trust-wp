// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `a % b` whose REMAINDER IS DISCARDED still panics when b = 0.
//! Creusot: `UInt32.rem` precondition `t'int b <> 0`.
//!
//! The `%` twin of `should_fail_div_zero_discarded`: the MIR
//! `Assert(RemainderByZero)` is the only site that can owe `b != 0` here.

use trust_wp::ensures;

#[ensures(true)]
pub fn rem0_discarded(a: u32, b: u32) {
    let _z = a % b;
}

fn main() {}
