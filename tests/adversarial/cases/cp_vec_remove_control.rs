//@ expect: verify
//@ mechanism: call pre/post scoping — over-refusal control
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: n/a (control) — the precondition gives the length, the postcondition gives the value.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() > 0)]
#[ensures(result == v@[0])]
pub fn vr_ok(mut v: Vec<u8>) -> u8 {
    v.remove(0)
}
