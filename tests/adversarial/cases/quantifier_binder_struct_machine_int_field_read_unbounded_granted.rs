//@ expect: reject
//@ mechanism: a binder over a struct with a `u8` field: `p.x` is below 256 for every `P`. Were the
//@ mechanism: field read over the unbounded integers the quantifier would be false, and `f`, which
//@ mechanism: returns false, credited. A sideways guard of D-203: the field's range is a premise.
//@ fixed-by: n/a (never accepted: a sideways guard of D-203)
//@ accept-means: `f` claims `result == true` in Rust's reading, returns false, and the crate exits 0.
//@ teeth: not shown: `f FAILED ✗ (postcondition)` with D-202 and with D-203 in force.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub x: u8,
}

#[ensures(result == (forall<p: P> p.x@ < 256))]
pub fn f() -> bool {
    false
}
