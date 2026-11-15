//@ expect: verify
//@ xfail: the price of D-136: an inlined call whose arguments call a function is refused, because the inlined body evaluates `needs_pos(y)` under `pick`'s branch and Creusot evaluates it once, before the call; the walk cannot place it, so the body is refused, true as it is. An inlined call whose arguments call nothing verifies (logic_fn_callee_precondition_inlined_call_plain_arguments_control.rs).
//@ mechanism: control for logic_fn_callee_precondition_inlined_argument_under_branch, differing in the caller's `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so the call inside the inlined call's argument holds wherever it is evaluated.
//@ accept-means: n/a (control) — `y > 0` wherever the caller may be called.
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

pub struct H;

impl H {
    #[logic(open)]
    pub fn pick(c: bool, z: Int) -> Int {
        if c {
            z
        } else {
            0
        }
    }
}

#[logic]
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    H::pick(false, needs_pos(y))
}
