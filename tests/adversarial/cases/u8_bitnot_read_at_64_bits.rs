//@ expect: reject
//@ verdict: failed
//@ fn-failed: not_bits
//@ mechanism: `!x` on a `u8` reaches the solver as a complement taken at 64 bits
//@ mechanism: (`encode_int_unop_bv_not` uses `DEFAULT_BV_WIDTH` whenever the operand is an integer
//@ mechanism: term; the driver's `UnOp::BitNot` carries no width). At `x == 0` the result is
//@ mechanism: `2^64 - 1`, not `255`, so the postcondition `result@ != 255` is proved.
//@ fixed-by: D-242: the complement is computed at the operand's type (`__trust_wp_int_bitop_u8`).
//@ accept-means: `not_bits(0)` returns `255`; an accept claims it does not.
//@ WHY THE CONTRACT IS FALSE: `not_bits(0) == 255`.
//@ teeth: ACCEPTED (`not_bits verified`), with and without D-142 (a contracted body is
//@ teeth: never capped). The twin u8_bitnot_control.rs states the true `result@ == 255`.
//@ teeth: ACCEPTED on trust-wp 7726ea81 (the parent of D-242); `not_bits FAILED` with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
#[ensures(result@ != 255)]
pub fn not_bits(x: u8) -> u8 {
    !x
}
