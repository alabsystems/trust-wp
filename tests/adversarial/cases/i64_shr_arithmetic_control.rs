//@ expect: verify
//@ mechanism: a signed `>>` is arithmetic: `-2i64 >> 1 == -1`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == -2)]
#[ensures(result@ == -1)]
pub fn half(x: i64) -> i64 {
    x >> 1
}
