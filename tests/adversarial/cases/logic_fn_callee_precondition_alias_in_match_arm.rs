//@ expect: reject
//@ mechanism: the match-arm spelling of logic_fn_callee_precondition_use_alias: the renamed call `np(v)` sits in the `Some(v)` arm of a `match`, where the walk owes a precondition under the arm's pattern with `v` bound by it. The spelling names no definition, so the walk (which reads a call's SPELLING, D-120) owed nothing there. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition in a match arm, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `o == Some(0)` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition in the arm and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_alias_in_match_arm_control.rs.
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

use crate::needs_pos as np;

#[logic]
#[ensures(true)]
pub fn caller(o: Option<Int>) -> Int {
    match o {
        Some(v) => np(v),
        None => 0,
    }
}
