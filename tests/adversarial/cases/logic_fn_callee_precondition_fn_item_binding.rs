//@ expect: reject
//@ mechanism: a fn item bound to a local and called through it: `let f = needs_pos; f(y)`. The call is spelled `f`, a name no definition carries, so the callee-precondition walk (which reads a call's SPELLING, D-120) owes nothing for it and the encoder reads `f` as an uninterpreted function. rustc types the local as `needs_pos`'s fn item, so the call denotes `needs_pos`. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition, through a local its fn item is bound to, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_fn_item_binding_control.rs.
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

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    let f = needs_pos;
    f(y)
}
