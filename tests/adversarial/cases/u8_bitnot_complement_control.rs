//@ expect: verify
//@ mechanism: `!x == 255 - x` on a `u8` at its type (D-242); unknown on trust-wp 7726ea81.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 255 - x@)]
pub fn not(x: u8) -> u8 {
    !x
}
