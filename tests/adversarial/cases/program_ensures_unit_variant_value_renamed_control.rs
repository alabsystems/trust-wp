//@ expect: verify
//@ mechanism: control for program_ensures_unit_variant_value_renamed, differing in the `use` alone: `use E::B;` makes `B` the variant `E::B` that `prog` returns.
//@ accept-means: n/a (control) — `result == B` holds.
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

#[ensures(result == B)]
pub fn prog() -> E {
    E::B
}
