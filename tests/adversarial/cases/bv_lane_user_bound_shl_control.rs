//@ expect: verify
//@ mechanism: twin of bv_lane_user_bound_wider_than_type_shl.rs where `x@ <= 15` keeps `x << 4` in
//@ mechanism: the `u8`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn times16(a: Int) -> Int {
    a * 16
}

#[requires(x@ <= 15)]
#[ensures(result@ == times16(x@))]
pub fn times(x: u8) -> u8 {
    x << 4
}
