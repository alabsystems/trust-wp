//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_inner_ensures_insufficient, differing in the caller's `#[requires]` alone: with `y > 1` the inner call's `ensures` makes the outer argument `y - 1 > 0`, so the goal is proved only by assuming the inner callee's `ensures` where its own precondition holds.
//@ accept-means: n/a (control) — `needs_pos(y) - 1 == y - 1 > 0` wherever `y > 1`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
#[ensures(result == x)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[requires(y > 1)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    needs_pos(needs_pos(y) - 1)
}
