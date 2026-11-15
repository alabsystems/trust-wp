//@ expect: reject
//@ mechanism: the general encoder read a machine bit operation at 64 bits with an unsigned
//@ mechanism: `bv2int`: an `i128` `x >> 1` was a LOGICAL 64-bit shift of the low 64 bits, read back
//@ mechanism: unsigned, so it was never negative. Rust's signed `>>` is arithmetic.
//@ accept-means: `half(-2^66) == -2^65 < 0`.
//@ WHY THE CONTRACT IS FALSE: `(-73786976294838206464i128) >> 1 == -36893488147419103232`.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`half verified`) on trust-wp 7726ea81; `unknown` with D-242, which computes the
//@ teeth: `>>` as the 128-bit arithmetic shift (`bvashr`): the counterexample is not validated
//@ teeth: through that bridge, so the rejection is not a `failed`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0 - 4294967296 * 4294967296 * 4)]
#[ensures(result@ >= 0)]
pub fn half(x: i128) -> i128 {
    x >> 1
}
