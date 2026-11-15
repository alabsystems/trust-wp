//@ expect: reject
//@ mechanism: the general encoder read a machine bit operation at 64 bits with an unsigned `bv2int`
//@ mechanism: (`encode_int_binop_bv`, `DEFAULT_BV_WIDTH`): `x << 1` on a `u8` kept the bit shifted
//@ mechanism: out of the type, so it equalled `x@ * 2` for every `x`. Since D-242 the driver lowers
//@ mechanism: the shift as `__trust_wp_int_bitop_u8(x << 1)`, computed at 8 bits.
//@ accept-means: `double(200) == 144`, not 400.
//@ WHY THE CONTRACT IS FALSE: `200u8 << 1 == 144` (Rust's `<<` checks only the amount).
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`double verified`) on trust-wp 7726ea81 (r30 verifier, g5_u8shl); not verified
//@ teeth: with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@ * 2)]
pub fn double(x: u8) -> u8 {
    x << 1
}
