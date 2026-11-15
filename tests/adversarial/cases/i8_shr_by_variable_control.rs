//@ expect: verify
//@ mechanism: twin of i8_shr_by_variable_read_as_logical.rs: a signed `>>` by a variable amount is
//@ mechanism: arithmetic at its type (D-242), `-128i8 >> 1 == -64`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == -128)]
#[requires(s@ == 1)]
#[ensures(result@ == -64)]
pub fn shift(x: i8, s: u32) -> i8 {
    x >> s
}
