//@ expect: reject
//@ mechanism: the general encoder read a machine bit operation at 64 bits with an unsigned
//@ mechanism: `bv2int`: `x << 64` on a `u128` was a 64-bit `bvshl` by 64, i.e. 0.
//@ accept-means: `shl64(1) == 2^64`.
//@ WHY THE CONTRACT IS FALSE: `1u128 << 64 == 18446744073709551616`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`shl64 verified`) on trust-wp 7726ea81 (r30 verifier, u128_shl64_lit); not
//@ teeth: verified with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ <= 4294967296 * 4294967296 - 1)]
#[ensures(result@ <= 4294967296 * 4294967296 - 1)]
pub fn shl64(x: u128) -> u128 {
    x << 64
}
