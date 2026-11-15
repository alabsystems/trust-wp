//@ expect: verify
//@ xfail: the price of D-136: an inlined call whose arguments call a function is refused, because inlining drops the argument `ignore` never reads and Creusot evaluates it once, before the call; the walk cannot place it, so the body is refused, true as it is. An inlined call whose arguments call nothing verifies (logic_fn_callee_precondition_inlined_call_plain_arguments_control.rs).
//@ mechanism: control for logic_fn_callee_precondition_inlined_argument_dropped_refilled, differing in the caller's `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so the call inside the dropped argument holds.
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
    pub fn ignore(z: Int) -> Int {
        needs_pos(1)
    }
}

#[logic]
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    H::ignore(needs_pos(y))
}
