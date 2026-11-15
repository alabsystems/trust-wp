//@ expect: reject
//@ mechanism: the builtin-name spelling of logic_fn_callee_precondition_use_alias: `use crate::needs_pos as abs;` renames the callee to a name the encoder already gives a meaning of its own, so the call `abs(y)` names no crate definition and the callee-precondition walk (which reads a call's SPELLING, D-120) owes nothing for it. A fix that resolves only names the encoder does not know misses a rename onto one it does. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition, through a rename onto a builtin's name, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_alias_to_builtin_name_control.rs.
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

use crate::needs_pos as abs;

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    abs(y)
}
