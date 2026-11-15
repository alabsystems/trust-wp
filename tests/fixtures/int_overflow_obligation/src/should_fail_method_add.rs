// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: method-syntax `x.add(1)` panics for `x = 255` in debug builds.

use std::ops::Add;
use trust_wp::ensures;

#[ensures(true)]
pub fn method_add(x: u8) -> u8 {
    x.add(1)
}

fn main() {}
