//@ expect: reject
//@ verdict: failed
//@ fn-failed: flip_lt
//@ mechanism: the tier-1 native QF_BV lane (bitwise_bv_proof) encoded `five() < result@` as
//@ mechanism: `x >> 6 < 5` (operands swapped, operator kept), a tautology over a `u8`.
//@ accept-means: `flip_lt(x)` is at most 3, so `5 < flip_lt(x)` is false for every `x`.
//@ WHY THE CONTRACT IS FALSE: `x >> 6 <= 3 < 5`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`flip_lt verified`) on trust-wp 7726ea81; FAILED once the operand order is
//@ teeth: kept.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn five() -> Int {
    5
}

#[ensures(five() < result@)]
pub fn flip_lt(x: u8) -> u8 {
    x >> 6
}
