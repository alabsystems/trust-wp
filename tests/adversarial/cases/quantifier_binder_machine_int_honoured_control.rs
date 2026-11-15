//@ expect: verify
//@ mechanism: control: every `u8` is below 256, and `f` returns true.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-199 in force,
//@ teeth: verified with D-203)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (forall<x: u8> x@ < 256))]
pub fn f() -> bool {
    true
}
