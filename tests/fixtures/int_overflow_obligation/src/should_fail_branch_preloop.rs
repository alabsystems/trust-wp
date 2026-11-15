// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED (pre-loop join): a local assigned on two pre-loop branches must not be
//! read in the loop at whichever branch the walk visited last.

use trust_wp::ensures;

#[ensures(true)]
pub fn joined(c: bool) -> u8 {
    let x: u8 = if c { 200 } else { 0 };
    let mut j: u8 = 0;
    let mut y: u8 = 0;
    while j < 3 {
        y = x + 100;
        j += 1;
    }
    y
}

fn main() {}
