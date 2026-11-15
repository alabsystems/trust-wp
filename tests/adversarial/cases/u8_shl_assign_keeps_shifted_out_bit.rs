//@ expect: reject
//@ mechanism: the compound-assignment spelling of u8_shl_doubling_read_without_dropping_bit.rs:
//@ mechanism: `y <<= 1` on a `u8` is the same MIR `<<`, read at 64 bits before D-242, so it kept
//@ mechanism: the bit shifted out of the type and equalled `x@ * 2` for every `x`.
//@ accept-means: `double(200) == 144`; an accept claims it is 400.
//@ WHY THE CONTRACT IS FALSE: `200u8 << 1 == 144`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`double verified`) on trust-wp 7726ea81; not verified with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@ * 2)]
pub fn double(x: u8) -> u8 {
    let mut y = x;
    y <<= 1;
    y
}
