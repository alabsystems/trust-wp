//@ expect: reject
//@ mechanism: a call inside an argument of a call the verifier inlines. `H::pick` is an open associated logic function with no contract, so `extract_logic_fn_defs` replaces `H::pick(false, needs_pos(y))` by `pick`'s body with the arguments substituted for its parameters: `if false { needs_pos(y) } else { 0 }`. The callee-precondition walk reads that inlined body, where the argument now sits under `pick`'s branch, and owes `needs_pos`'s precondition only where the branch holds: `false ==> y > 0`. Creusot's logic vcgen evaluates a call's arguments before the call, wherever the callee uses them. Found probing sideways from D-136's counting, which reads the parsed body the same way.
//@ accept-means: a logic function that calls another outside its precondition, inside an argument of an inlined call, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` the body evaluates the argument `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, on the rustc-resolution walk that reads the inlined body: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_inlined_argument_under_branch_control.rs.
//@ fixed-by: D-136
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
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    H::pick(false, needs_pos(y))
}
