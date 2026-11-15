//@ expect: verify
//@ mechanism: a signed `!` at its type: `!x == -x - 1`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == -x@ - 1)]
pub fn not(x: i8) -> i8 {
    !x
}
