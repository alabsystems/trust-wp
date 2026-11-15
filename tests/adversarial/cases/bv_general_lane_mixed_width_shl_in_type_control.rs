//@ expect: verify
//@ mechanism: twin of bv_general_lane_mixed_width_shl_reads_product.rs where `x@ <= 15` keeps the
//@ mechanism: `u8` shift inside the type: in the tier-2 lane's 16-bit window the machine `<<` is
//@ mechanism: then the exact product (D-242), as the bare shift was before.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ <= 15)]
#[ensures(result@ == x@ * 16)]
pub fn widen(x: u8, y: u16) -> u16 {
    ((x << 4) as u16) | (y & 0)
}
