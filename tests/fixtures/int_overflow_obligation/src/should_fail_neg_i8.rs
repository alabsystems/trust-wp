// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `-x` on `i8` with no precondition can overflow (x = -128).
//! Creusot: `Int8.neg` precondition `to_int a <> min_int`.

use trust_wp::ensures;

#[ensures(true)]
pub fn negate(x: i8) -> i8 {
    -x
}

fn main() {}
