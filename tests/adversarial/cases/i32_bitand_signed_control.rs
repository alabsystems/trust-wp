//@ expect: verify
//@ mechanism: signed `|` and `&` at their type keep a negative value: `(x | 0) & (x | 0) == x`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == x)]
pub fn same(x: i32) -> i32 {
    (x | 0) & (x | 0)
}
