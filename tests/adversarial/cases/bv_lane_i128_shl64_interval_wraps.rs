//@ expect: reject
//@ mechanism: the tier-1 native QF_BV lane (bitwise_bv_proof)'s interval bounded `a << s` with
//@ mechanism: `i128::checked_shl`, which checks only the shift COUNT: `(2^64 - 1).checked_shl(64)`
//@ mechanism: is `Some(-2^64)`, a negative upper bound that certified the node inside the 64-bit
//@ mechanism: window and skipped its wrap guard, so the 64-bit `bvshl` (0) was taken as the value
//@ mechanism: of `x << 64`.
//@ accept-means: `shl64(1) == 2^64` (no overflow: 64 < 128), so `result@ == 0` is false.
//@ WHY THE CONTRACT IS FALSE: `1i128 << 64 == 18446744073709551616`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`shl64 verified`) on trust-wp 7726ea81 (r30 verifier, i128_shl64); not verified
//@ teeth: once the interval multiplies by `2^s` with a checked product.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn zero() -> Int {
    0
}

#[requires(x >= 0)]
#[requires(x@ <= 4294967296 * 4294967296 - 1)]
#[ensures(result@ == zero())]
pub fn shl64(x: i128) -> i128 {
    x << 64
}
