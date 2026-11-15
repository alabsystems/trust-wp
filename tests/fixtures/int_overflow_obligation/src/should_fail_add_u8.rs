// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `x + 1` on `u8` with no precondition can overflow (x = 255).
//! Creusot: `UInt8.add` precondition `in_bounds (x + 1)` — unprovable.

use trust_wp::ensures;

#[ensures(true)]
pub fn add_one(x: u8) -> u8 {
    x + 1
}

fn main() {}
