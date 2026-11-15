//@ expect: reject
//@ mechanism: a call inside an argument the inlined callee never reads, beside a same-spelled call in that callee's body. `H::ignore` is an open associated logic function with no contract, so `extract_logic_fn_defs` replaces `H::ignore(needs_pos(y))` by `ignore`'s body, `needs_pos(1)`, and the argument, which `ignore` never reads, is gone. D-136's check that every call of the type-checked body that owes a precondition has a counterpart counted the INLINED body's `needs_pos(1)` as the counterpart of the argument's `needs_pos(y)`, and the walk owed `1 > 0`. Creusot's logic vcgen evaluates a call's arguments before the call, read or not. Found probing sideways from D-136's counting.
//@ accept-means: a logic function that calls another outside its precondition, inside an argument an inlined call drops, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` the body evaluates the argument `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, on the rustc-resolution walk that counts the inlined body: `creusot_test::caller verified ✓`. With `ignore`'s body `0` the same build refuses the caller (no counterpart). The control is logic_fn_callee_precondition_inlined_argument_dropped_refilled_control.rs.
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
    pub fn ignore(z: Int) -> Int {
        needs_pos(1)
    }
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    H::ignore(needs_pos(y))
}
