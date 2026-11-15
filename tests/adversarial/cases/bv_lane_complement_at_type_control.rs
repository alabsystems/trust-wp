//@ expect: verify
//@ mechanism: `!x == 255 - x` on a `u8`, at its type in the tier-1 lane (D-242); FAILED on
//@ mechanism: trust-wp 7726ea81.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn comp(a: Int) -> Int {
    255 - a
}

#[ensures(result@ == comp(x@))]
pub fn complement(x: u8) -> u8 {
    !x
}
