//@ expect: reject
//@ mechanism: the general encoder read a machine bit operation at 64 bits with an unsigned
//@ mechanism: `bv2int`: `!x` on a `u128` was complemented at 64 bits, so it never exceeded
//@ mechanism: `2^64 - 1`.
//@ accept-means: `not(0) == 2^128 - 1`.
//@ WHY THE CONTRACT IS FALSE: `!0u128 == u128::MAX`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`not verified`) on trust-wp 7726ea81; not verified with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ <= 4294967296 * 4294967296 - 1)]
pub fn not(x: u128) -> u128 {
    !x
}
