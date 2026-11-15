//@ expect: verify
//@ mechanism: an unsuffixed float literal in a contract has the type its context infers, so `0.1` beside an
//@ mechanism: `f32` result is `0.1f32`: the decimal rounded directly to binary32, which is what the body returns.
//@ accept-means: n/a (control) — `tenth()` returns `0.1f32`, the value the contract names.
//@ fixed-by: n/a (control)
//@ teeth: failed on the commit before D-215 (the literal was the real 0.1 and the result the real value of
//@ teeth: `0.1f32`); verified after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 0.1)]
pub fn tenth() -> f32 {
    0.1
}
