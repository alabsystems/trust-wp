//@ expect: verify
//@ mechanism: control for logic_fn_body_unit_variant_value_renamed, differing in the `use` alone: `use E::B;` makes the body the variant `E::B`.
//@ accept-means: n/a (control) — `caller()` is `E::B`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(PartialEq, Eq)]
pub enum E {
    A,
    B,
}

use E::B;

#[logic]
#[ensures(result == E::B)]
pub fn caller() -> E {
    B
}
