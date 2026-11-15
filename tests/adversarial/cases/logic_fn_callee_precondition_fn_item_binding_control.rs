//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_fn_item_binding, differing in the caller's `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so a fix that owes the precondition of the fn item a local is bound to must still verify it.
//@ accept-means: n/a (control) — the call through the local is inside the callee's precondition wherever the caller may be called.
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
    let f = needs_pos;
    f(y)
}
