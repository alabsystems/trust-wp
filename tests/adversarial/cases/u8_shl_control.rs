//@ expect: verify
//@ mechanism: twin of u8_shl_keeps_shifted_out_bit.rs whose postcondition is true.
//@ mechanism: Verified since D-242 reads the operation at its type; it was an xfail control before.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 128)]
#[ensures(result@ == 0)]
pub fn shl_bits(x: u8) -> u8 {
    x << 1
}
