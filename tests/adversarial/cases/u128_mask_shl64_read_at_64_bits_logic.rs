//@ expect: reject
//@ mechanism: the general encoder read a machine bit operation at 64 bits with an unsigned
//@ mechanism: `bv2int`: `(x & 3) << 64` on a `u128` was a 64-bit shift by 64, i.e. 0, so a
//@ mechanism: logic-function bound below `2^64` was proved.
//@ accept-means: `shl64(1) == 2^64 > m64()`.
//@ WHY THE CONTRACT IS FALSE: `(1u128 & 3) << 64 == 18446744073709551616`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`shl64 verified`) on trust-wp 7726ea81 (r30 verifier, u128_shl64_logic); not
//@ teeth: verified with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn m64() -> Int {
    4294967296 * 4294967296 - 1
}

#[requires(x@ <= 4294967296 * 4294967296 - 1)]
#[ensures(result@ <= m64())]
pub fn shl64(x: u128) -> u128 {
    (x & 3) << 64
}
