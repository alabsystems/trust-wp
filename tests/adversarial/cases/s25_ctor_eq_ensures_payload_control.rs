//@ expect: verify
//@ mechanism: constructor-equality payload facts — control (true enum postcondition)
//@ fixed-by: cfff9b4 (s25 vacuous whole-value equality)
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum E {
    A(i32),
    B,
}

#[ensures(result == E::A(2i32))]
pub fn enum_true() -> E {
    E::A(2i32)
}
