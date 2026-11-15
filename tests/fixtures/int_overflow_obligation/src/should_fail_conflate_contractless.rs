// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: contract-free; `b = a.wrapping_add(128)` read through the same
//! local, so `a - b` underflows for `input = 0`.

pub fn conflate_contractless(input: u8) -> u8 {
    let mut x: u8 = input;
    let a = x;
    x = x.wrapping_add(128);
    let b = x;
    let mut i: u8 = 0;
    while i < 1 {
        i += 1;
    }
    let _ = x;
    a - b
}

fn main() {}
