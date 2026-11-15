//@ expect: reject
//@ mechanism: the general encoder read a machine bit operation at 64 bits with an unsigned
//@ mechanism: `bv2int`: a `u128` operand was cut to its low 64 bits, so `x | 0` never exceeded
//@ mechanism: `2^64 - 1`.
//@ accept-means: `or0(2^64) == 2^64`.
//@ WHY THE CONTRACT IS FALSE: `x | 0 == x` for every `u128`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`or0 verified`) on trust-wp 7726ea81 (r30 verifier, g3_u128or); not verified
//@ teeth: with D-242, which computes the `|` at 128 bits.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ <= 4294967296 * 4294967296 - 1)]
pub fn or0(x: u128) -> u128 {
    x | 0
}
