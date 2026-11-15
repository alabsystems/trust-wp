//@ expect: reject
//@ mechanism: the `self::` spelling of logic_fn_callee_precondition_use_alias: module `m` renames `crate::needs_pos` to `np` and its logic function calls `self::np(y)`, whose last segment names no definition, so the callee-precondition walk (which reads a call's SPELLING, D-120) owes nothing for it. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition, through a renaming import named by a `self::` path, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `m::caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::m::caller verified ✓`.
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

pub mod m {
    use creusot_std::prelude::*;
    pub use crate::needs_pos as np;

    #[logic]
    #[ensures(true)]
    pub fn caller(y: Int) -> Int {
        self::np(y)
    }
}
