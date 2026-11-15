//@ expect: reject
//@ mechanism: the re-export spelling of logic_fn_callee_precondition_use_alias: `pub use crate::needs_pos as np;` in module `m` makes the call `m::np(y)`, whose last segment names no definition, so the callee-precondition walk owes nothing for it and the encoder reads it as an uninterpreted function. A fix that reads only the caller's own module's imports misses this one.
//@ accept-means: a logic function that calls another outside its precondition, through a renaming re-export, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-119: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_reexport_alias_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    pub use crate::needs_pos as np;
}

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    m::np(y)
}
