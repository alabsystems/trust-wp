//@ expect: reject
//@ mechanism: the tier-1 native QF_BV lane (bitwise_bv_proof) recovers its window W from the
//@ mechanism: `v@ <= 2^W - 1` premise it reads LAST: the user's `x@ <= 65535` on a `u8` gave W =
//@ mechanism: 16, and the bare `x << 4` was then read as the exact `x * 16` (it fits 16 bits),
//@ mechanism: although Rust drops the bits above the `u8`. Since D-242 the `<<` reaches the lane at
//@ mechanism: its type and is masked to 8 bits.
//@ accept-means: `times(16) == 0` (16 << 4 = 256 wraps to 0 in a u8), not `16 * 16`.
//@ WHY THE CONTRACT IS FALSE: `16u8 << 4 == 0`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`times verified`) on trust-wp 7726ea81; not verified with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn times16(a: Int) -> Int {
    a * 16
}

#[requires(x@ <= 65535)]
#[ensures(result@ == times16(x@))]
pub fn times(x: u8) -> u8 {
    x << 4
}
