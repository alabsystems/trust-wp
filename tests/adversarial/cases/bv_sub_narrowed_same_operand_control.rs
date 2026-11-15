//@ expect: verify
//@ mechanism: the over-refusal half of the isolating pair for D-115. The SWAR popcount step
//@ mechanism: `x - ((x >> 1) & 0x55)` subtracts a value the same `x` bounds: `(x >> 1) & 0x55` lies in
//@ mechanism: `[0, x]` for every u8 `x`, so the difference never leaves `[0, 255]`, the u8 overflow
//@ mechanism: check holds, and `result@ <= x@`. The native bit-vector lane's interval arithmetic
//@ mechanism: read the two operands as independent (`[-0x55, 255]`), called the difference inexact
//@ mechanism: and bailed, and the mixed Int/bit-vector encoding that took over did not decide it.
//@ accept-means: n/a (control) — this contract is TRUE for every u8 `x`.
//@ fixed-by: D-115
//@ teeth: `unknown` on a build with the narrowing rule switched off by a local knob, `verified` with
//@ teeth: it on; its false twin bv_sub_narrowed_other_operand_underflow.rs is `unknown` on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ <= x@)]
pub fn swar_step(x: u8) -> u8 {
    x - ((x >> 1) & 0x55)
}
