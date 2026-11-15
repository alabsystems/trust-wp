//@ expect: verify
//@ mechanism: `as` from an integer to a float rounds to nearest-even: 16777217 is not an `f32` value and
//@ mechanism: converts to 16777216. The real-number model read the cast as the identity.
//@ accept-means: n/a (control) — `16777217i32 as f32` is `16777216.0` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: failed on the commit before D-215 (a counterexample from reading the cast as the identity);
//@ teeth: verified after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 16777216.0)]
pub fn rounds() -> f32 {
    let n = 16777217i32;
    n as f32
}
