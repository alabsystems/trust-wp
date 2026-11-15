// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `Add::add(x, 1)` spelled as a path call is the same inherited-overflow
//! operation as `x + 1`; panics for `x = 255`.

use trust_wp::ensures;

#[ensures(true)]
pub fn explicit_add(x: u8) -> u8 {
    std::ops::Add::add(x, 1)
}

fn main() {}
