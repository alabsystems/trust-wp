//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_never_examined, differing in the caller's `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so the goal the logic lane owes for the call holds under the caller's own premise.
//@ accept-means: n/a (control) — the call is inside the callee's precondition wherever the caller may be called.
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
    needs_pos(y)
}
