//@ expect: verify
//@ mechanism: a signed `^` at its type keeps the sign (D-242): `-1i16 ^ 255 == -256`; read at 64
//@ mechanism: bits with an unsigned `bv2int` it was `2^64 - 256`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == -1)]
#[ensures(result@ == -256)]
pub fn flip_low(x: i16) -> i16 {
    x ^ 255
}
