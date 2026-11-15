//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_dropped_wildcard_scrutinee, differing in the call's argument alone: the kept scrutinee `needs_pos(1)` is inside the callee's precondition.
//@ accept-means: n/a (control) — `1 > 0` holds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    pearlite! { match needs_pos(1) { _ => y } }
}
