//@ expect: reject
//@ verdict: failed
//@ fn-failed: flip
//@ mechanism: the tier-1 native QF_BV lane (bitwise_bv_proof) compared `func <cmp> spec` whatever
//@ mechanism: side of the ensures `result` was on. For `five() <= result@` it checked `x & 0 <= 5`,
//@ mechanism: the opposite inequality, which holds.
//@ accept-means: `flip(x)` returns 0, and `5 <= 0` is false.
//@ WHY THE CONTRACT IS FALSE: `flip(x) == x & 0 == 0 < 5`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`flip verified`) on trust-wp 7726ea81; FAILED once the comparison keeps the
//@ teeth: ensures' operand order. Found by the r30 verifier (flip_logic).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn five() -> Int {
    5
}

#[ensures(five() <= result@)]
pub fn flip(x: u8) -> u8 {
    x & 0
}
