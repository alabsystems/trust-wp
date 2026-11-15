//@ expect: verify
//@ mechanism: the true `zero() <= result@` with the spec on the left; FAILED on trust-wp 7726ea81
//@ mechanism: (checked as `x >> 6 <= 0`).
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn zero() -> Int {
    0
}

#[ensures(zero() <= result@)]
pub fn flip(x: u8) -> u8 {
    x >> 6
}
