//@ expect: reject
//@ mechanism: the tier-1 native QF_BV lane (bitwise_bv_proof): the `u128` twin of
//@ mechanism: bv_lane_i128_shl64_interval_wraps.rs, the same `checked_shl` interval that checks the
//@ mechanism: count and not the value.
//@ accept-means: `shl64(1) == 2^64`, so `result@ == 0` is false.
//@ WHY THE CONTRACT IS FALSE: `1u128 << 64 == 18446744073709551616`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`shl64 verified`) on trust-wp 7726ea81; not verified with the checked product.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn zero() -> Int {
    0
}

#[requires(x@ <= 4294967296 * 4294967296 - 1)]
#[ensures(result@ == zero())]
pub fn shl64(x: u128) -> u128 {
    x << 64
}
