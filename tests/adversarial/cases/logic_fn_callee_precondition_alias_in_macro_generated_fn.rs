//@ expect: reject
//@ mechanism: the macro spelling of logic_fn_callee_precondition_use_alias: a `macro_rules!` item writes the logic function whose body calls `np(y)`, renamed by a `use` at the crate root. The contract macros see the expanded item, so its body is parsed and type-checked like any other; the walk that read a call's SPELLING (D-120) owed nothing, and rustc resolves the call to `needs_pos`. Found probing sideways from D-120.
//@ accept-means: a macro-generated logic function that calls another outside its precondition, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_callee_precondition_alias_in_macro_generated_fn_control.rs.
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

macro_rules! mk {
    ($name:ident) => {
        #[logic]
        #[ensures(true)]
        pub fn $name(y: Int) -> Int {
            np(y)
        }
    };
}

mk!(caller);
