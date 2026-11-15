//@ expect: reject
//@ verdict: failed
//@ fn-failed: shl_bits
//@ mechanism: `x << 1` on a `u8` is read without dropping the bits shifted out of the type: at
//@ mechanism: `x == 128` it is `256`. Rust's shift checks only its amount (`1 < 8` here) and
//@ mechanism: discards the high bit, so the result is `0`; the postcondition `result@ != 0` is proved.
//@ fixed-by: D-242: the shift is computed at the operand's type (`__trust_wp_int_bitop_u8`), which
//@ fixed-by: drops the bit shifted out.
//@ accept-means: `shl_bits(128)` returns `0`; an accept claims it does not.
//@ WHY THE CONTRACT IS FALSE: `shl_bits(128) == 0`.
//@ teeth: ACCEPTED (`shl_bits verified`), with and without D-142. The twin
//@ teeth: u8_shl_control.rs states the true `result@ == 0`.
//@ teeth: ACCEPTED on trust-wp 7726ea81 (the parent of D-242); `shl_bits FAILED` with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 128)]
#[ensures(result@ != 0)]
pub fn shl_bits(x: u8) -> u8 {
    x << 1
}
