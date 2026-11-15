// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `AddAssign::add_assign(&mut x, 1)` panics for `x = 255`.

use std::ops::AddAssign;
use trust_wp::ensures;

#[ensures(true)]
pub fn explicit_add_assign(mut x: u8) -> u8 {
    AddAssign::add_assign(&mut x, 1);
    x
}

fn main() {}
