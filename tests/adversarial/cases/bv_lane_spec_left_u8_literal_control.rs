//@ expect: verify
//@ mechanism: a machine literal on the left: `3u8 >= result` over `x & 3`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(3u8 >= result)]
pub fn flip(x: u8) -> u8 {
    x & 3
}
