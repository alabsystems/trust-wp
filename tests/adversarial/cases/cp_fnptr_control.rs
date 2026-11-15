//@ expect: verify
//@ mechanism: indirect call — over-refusal control
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: n/a (control) — the target's precondition is true and its postcondition gives the result.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(true)]
#[ensures(result == x)]
pub fn id(x: u8) -> u8 {
    x
}

#[ensures(result == x)]
pub fn fnptr_ok(x: u8) -> u8 {
    let f: fn(u8) -> u8 = id;
    f(x)
}
