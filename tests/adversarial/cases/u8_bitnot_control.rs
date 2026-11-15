//@ expect: verify
//@ mechanism: twin of u8_bitnot_read_at_64_bits.rs whose postcondition is true.
//@ mechanism: Verified since D-242 reads the operation at its type; it was an xfail control before.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
#[ensures(result@ == 255)]
pub fn not_bits(x: u8) -> u8 {
    !x
}
