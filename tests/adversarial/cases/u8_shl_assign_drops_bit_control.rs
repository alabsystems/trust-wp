//@ expect: verify
//@ mechanism: twin of u8_shl_assign_keeps_shifted_out_bit.rs: `200u8 <<= 1` leaves 144 (D-242).
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 200)]
#[ensures(result@ == 144)]
pub fn double(x: u8) -> u8 {
    let mut y = x;
    y <<= 1;
    y
}
