//@ expect: verify
//@ mechanism: a derived `Default` for an enum whose default variant carries a payload states each field's default (Creusot's derive does), so a caller may read `x == 0` off it; it is also proved, not `#[trusted]`
//@ xfail: `first` ends `unknown` (quantifier-unhandled, or a timeout under load): the caller does not yet read the payload fields off the derived default's match-shaped postcondition
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use creusot_std::prelude::Default;

#[derive(Default)]
pub enum E {
    #[default]
    A(i32, i32),
    B,
}

#[ensures(result == 0i32)]
pub fn first() -> i32 {
    match E::default() {
        E::A(x, _) => x,
        E::B => 1i32,
    }
}
