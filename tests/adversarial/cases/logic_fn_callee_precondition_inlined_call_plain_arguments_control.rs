//@ expect: verify
//@ mechanism: control for the inlined-argument refusals (logic_fn_callee_precondition_inlined_argument_under_branch.rs, logic_fn_callee_precondition_inlined_argument_dropped_refilled.rs): an inlined call whose arguments call nothing has no argument whose precondition the inlined body could move or drop, and a call beside it owes its own precondition at its own arguments.
//@ accept-means: n/a (control) — `y > 0` wherever the caller may be called, and `H::pick`'s arguments call nothing.
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
    needs_pos(y) + H::pick(false, y)
}
