// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: the conflated `a - b` inside a loop without an invariant.

use trust_wp::{ensures, requires};

#[requires(input@ == 0)]
#[ensures(true)]
pub fn conflate_loop(input: u8) -> u8 {
    let mut x: u8 = input;
    let a = x;
    x = 255;
    let b = x;
    let mut i: u8 = 0;
    let mut r: u8 = 0;
    while i < 1 {
        r = a - b;
        i += 1;
    }
    let _ = x;
    r
}

fn main() {}
