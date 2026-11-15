//@ expect: verify
//@ mechanism: `(x & 15) << 4` on a `u8` stays below 241, proved at its type in the tier-1 lane.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn cap() -> Int {
    240
}

#[ensures(result@ <= cap())]
pub fn pack(x: u8) -> u8 {
    (x & 15) << 4
}
