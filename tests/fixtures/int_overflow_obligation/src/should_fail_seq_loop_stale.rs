// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED (sequential loops): a local written by an EARLIER loop must not keep
//! its one-iteration value when a later loop body reads it.

use trust_wp::ensures;

#[ensures(true)]
pub fn two_loops() -> u8 {
    let mut x: u8 = 0;
    while x < 10 {
        x += 1;
    }
    let mut j: u8 = 0;
    let mut y: u8 = 0;
    while j < 3 {
        y = x + 250;
        j += 1;
    }
    y
}

fn main() {}
