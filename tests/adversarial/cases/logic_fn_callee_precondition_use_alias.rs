//@ expect: reject
//@ mechanism: the callee-precondition walk (`logic_fn_verify::callee_preconditions`) decides which contracted definitions a logic call may denote from the call's SPELLING alone (`may_denote`: the exact symbol, the crate path, or a last path segment equal to the definition's name). A `use crate::needs_pos as np;` renames the call to `np(y)`: no definition is named `np`, so the walk owes nothing, and the encoder reads `np` as an uninterpreted function, so the ensures lane proves `true` as before. Rust resolves `np` to `needs_pos`, and so does Creusot. Found probing sideways from D-119.
//@ accept-means: a logic function that calls another outside its precondition, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-119: `creusot_test::caller verified ✓`. The same file spelling the call `needs_pos(y)` is logic_fn_callee_precondition_never_examined.rs, which D-119 rejects. The re-export spelling is logic_fn_callee_precondition_reexport_alias.rs; the control is logic_fn_callee_precondition_use_alias_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use crate::needs_pos as np;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    np(y)
}
