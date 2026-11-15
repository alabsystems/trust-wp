//@ expect: reject
//@ mechanism: the quantifier spelling of logic_fn_callee_precondition_use_alias: the renamed call `np(z)` sits under `forall<z: Int>`, where the walk owes a precondition for every value of the binder. The spelling names no definition, so the walk that read a call's SPELLING (D-120) owed nothing there; rustc resolves the call to `needs_pos` in the body's type-check closure. Found probing sideways from D-120.
//@ accept-means: a logic function whose quantified body calls another outside its precondition, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `z == 0` the body evaluates `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition under the binder and is invalid.
//@ teeth: MEASURED with D-120 open: not credited, but only because the encoder did not know the renamed callee's sort (`demoted: encoding approximations may affect soundness: sort_fallback_to_int_from_logic_fn(1)`), which demoted the control too; no lane owed the call. With D-136 the call is read as `needs_pos`: this case FAILS on the callee precondition and the control verifies. The control is logic_fn_callee_precondition_alias_under_quantifier_control.rs.
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
pub fn caller(y: Int) -> bool {
    pearlite! { forall<z: Int> np(z) == z }
}
