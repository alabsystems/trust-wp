// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `a` and `b` are read from the same local at two program points
//! (`a == 0`, `b == 255`). A seed that binds both to one havoc of `x`
//! assumes `a == b` and discharges `a - b` (panics at runtime).

use trust_wp::{ensures, requires};

#[requires(input@ == 0)]
#[ensures(true)]
pub fn conflate_post(input: u8) -> u8 {
    let mut x: u8 = input;
    let a = x;
    x = 255;
    let b = x;
    let mut i: u8 = 0;
    while i < 1 {
        i += 1;
    }
    let _ = x;
    a - b
}

fn main() {}
