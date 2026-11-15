//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_dropped_tuple_component, differing in the caller's `#[requires]` alone: the component kept for its call is inside `needs_pos`'s precondition.
//@ accept-means: n/a (control) — `y > 0` puts the evaluated call inside the callee's precondition.
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
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    pearlite! { (needs_pos(y), 1).1 }
}
