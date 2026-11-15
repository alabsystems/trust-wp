// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: contract-free; `assert!(x < 3)` panics for `x = 3`. Only its
//! arithmetic goal `x + 1` holds: the function must never be `verified`.

pub fn assert_contractless(x: u8) -> u8 {
    assert!(x < 3);
    x + 1
}

fn main() {}
