//@ expect: verify
//@ mechanism: twin of u8_shl_doubling_read_without_dropping_bit.rs where `x@ < 128` keeps the bit.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 128)]
#[ensures(result@ == x@ * 2)]
pub fn double(x: u8) -> u8 {
    x << 1
}
