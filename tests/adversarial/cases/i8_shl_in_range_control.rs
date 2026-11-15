//@ expect: verify
//@ mechanism: a signed `<<` at its type: `x << 1 == 2x` for `-64 <= x < 64`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ >= -64 && x@ < 64)]
#[ensures(result@ == x@ * 2)]
pub fn double(x: i8) -> i8 {
    x << 1
}
