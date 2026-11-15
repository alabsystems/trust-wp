//@ expect: reject
//@ mechanism: the tier-2 native QF_BV lane (bitwise_bv_proof_general) takes the smallest window
//@ mechanism: covering every operand: with a `u8` and a `u16` that is 16 bits, and the bare
//@ mechanism: `x << 4` was read as the exact product `x * 16` there although the `u8` shift drops
//@ mechanism: the bits above 8. Since D-242 the `<<` reaches the lane at its type, and in a window
//@ mechanism: wider than the type it is read only where it cannot wrap at the type (`x@ <= 15` in
//@ mechanism: bv_general_lane_mixed_width_shl_in_type_control.rs); here it can, so the lane bails.
//@ accept-means: `widen(16, y) == 0`, not 256.
//@ WHY THE CONTRACT IS FALSE: `16u8 << 4 == 0`, and the widening cast keeps 0.
//@ fixed-by: D-242 (trust-wp fix(bv-lane): read a machine bit operation at its type, and keep the
//@ fixed-by: ensures' operand order)
//@ teeth: ACCEPTED (`widen verified`) on trust-wp 7726ea81; not verified with D-242.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@ * 16)]
pub fn widen(x: u8, y: u16) -> u16 {
    ((x << 4) as u16) | (y & 0)
}
