//@ expect: verify
//@ mechanism: control for program_ensures_variant_pattern_renamed, differing in the `use` alone: `use E::B;` makes the pattern `B(_)` the variant `E::B`, which `E::A(0)` does not match.
//@ accept-means: n/a (control) — the catch-all arm is taken and the postcondition is `true`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E {
    A(u32),
    B(u32),
}

use E::B;

#[ensures(match result { B(_) => false, _ => true })]
pub fn prog() -> E {
    E::A(0)
}
