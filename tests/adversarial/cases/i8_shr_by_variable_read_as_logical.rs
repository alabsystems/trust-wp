//@ expect: reject
//@ mechanism: the general encoder read a machine `>>` at 64 bits with an unsigned `bv2int`, so a
//@ mechanism: signed `x >> s` by a VARIABLE amount was a logical shift of the operand's 64-bit
//@ mechanism: pattern read back unsigned: never negative. Rust's signed `>>` is arithmetic. Since
//@ mechanism: D-242 the driver lowers it as `__trust_wp_int_bitop_s8(x >> s)`, a `bvashr` at 8
//@ mechanism: bits.
//@ accept-means: `shift(-128, 1) == -64`; an accept claims it is non-negative.
//@ WHY THE CONTRACT IS FALSE: `-128i8 >> s` is negative for every `s < 8`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`shift verified`) on trust-wp 7726ea81; not verified with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == -128)]
#[requires(s@ < 8)]
#[ensures(result@ >= 0)]
pub fn shift(x: i8, s: u32) -> i8 {
    x >> s
}
