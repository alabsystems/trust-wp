//@ expect: reject
//@ mechanism: the glob spelling of logic_fn_callee_precondition_reexport_alias: `pub use crate::needs_pos as np;` in module `m` and `use m::*;` at the root make the call `np(y)`, which names no definition, so the callee-precondition walk (which reads a call's SPELLING, D-120) owes nothing for it and the encoder reads `np` as an uninterpreted function. A fix that follows only the caller's own module's named imports misses a glob. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition, through a renaming re-export reached by a glob import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    pub use crate::needs_pos as np;
}
use m::*;

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
