//@ expect: verify
//@ mechanism: `200u8 << 1 == 144`; FAILED (a wrong refutation) on trust-wp 7726ea81, which read
//@ mechanism: 400.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 200)]
#[ensures(result@ == 144)]
pub fn double(x: u8) -> u8 {
    x << 1
}
