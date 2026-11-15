//@ expect: verify
//@ mechanism: twin of bv_lane_spec_left_le_read_as_func_le_spec.rs with the true
//@ mechanism: `five() >= result@`; FAILED (a wrong refutation) on trust-wp 7726ea81, where the
//@ mechanism: swapped operands checked `x & 3 >= 5`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn five() -> Int {
    5
}

#[ensures(five() >= result@)]
pub fn flip(x: u8) -> u8 {
    x & 3
}
