//@ expect: reject
//@ verdict: failed
//@ fn-failed: complement
//@ mechanism: the tier-1 native QF_BV lane (bitwise_bv_proof) with the spec on the left:
//@ mechanism: `comp(x@) < result@` over `!x` was checked as `!x < 255 - x`. (The `!` itself reaches
//@ mechanism: the lane at its type since D-242.)
//@ accept-means: `complement(x) == 255 - x`, never greater than `comp(x@) == 255 - x@`.
//@ WHY THE CONTRACT IS FALSE: `!x == 255 - x` for a `u8`, so `255 - x < 255 - x` is false.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`complement verified`) on trust-wp 7726ea81; FAILED with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn comp(a: Int) -> Int {
    255 - a
}

#[ensures(comp(x@) < result@)]
pub fn complement(x: u8) -> u8 {
    !x
}
