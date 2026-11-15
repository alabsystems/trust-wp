//@ expect: reject
//@ mechanism: the block-scoped spelling of logic_fn_callee_precondition_use_alias: the logic body itself declares `use crate::needs_pos as np;` and calls `np(y)`. A fix that resolves a call through the caller's module's imports misses an item declared in the body; rustc resolves it all the same. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition, through a renaming import its own body declares, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`.
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
    use crate::needs_pos as np;
    np(y)
}
