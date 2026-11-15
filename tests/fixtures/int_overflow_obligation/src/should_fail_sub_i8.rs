// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `x - 1` on `i8` with no precondition can overflow (x = -128).

use trust_wp::ensures;

#[ensures(true)]
pub fn dec(x: i8) -> i8 {
    x - 1
}

fn main() {}
