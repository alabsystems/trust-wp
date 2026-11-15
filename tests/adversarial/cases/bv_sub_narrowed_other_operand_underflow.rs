//@ expect: reject
//@ verdict: unknown
//@ mechanism: the false half of the isolating pair for D-115: bv_sub_narrowed_same_operand_control
//@ mechanism: with the shifted operand read from a second parameter. D-115 lets the native
//@ mechanism: bit-vector lane bound `l - r` below by 0 only when `r` is `l` itself narrowed by right
//@ mechanism: shifts and non-negative masks; here `r` narrows `y`, not `x`, so nothing bounds the
//@ mechanism: difference and the u8 subtraction underflows. A narrowing rule that matched the shape
//@ mechanism: and not the operand proves the overflow check. The function has no contract, so the
//@ mechanism: overflow check is its only obligation.
//@ accept-means: `swar_step(0, 2)` computes `0 - ((2 >> 1) & 0x55) = 0 - 1` in u8 and panics; an
//@ accept-means: accept claims it returns.
//@ fixed-by: n/a (shape gate for D-115)
//@ teeth: ACCEPTED on a local build whose `narrowed_from` answered true for every shape; `unknown`
//@ teeth: with the rule as D-115 states it and with the rule switched off.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn swar_step(x: u8, y: u8) -> u8 {
    x - ((y >> 1) & 0x55)
}
