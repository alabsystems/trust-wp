//@ expect: reject
//@ mechanism: the renaming-import spelling of logic_fn_program_callee_precondition: the walk refuses a logic call that may denote a program function with a precondition by matching the call's spelling against the program function's names (`ProgramFnsWithRequires::may_denote`); `use crate::prog as p;` makes the call `p(y)`, which matches none, and the encoder reads it as a placeholder. Creusot resolves `p` to `prog` and rejects the crate.
//@ accept-means: a logic function that calls a program function outside its precondition, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` the body calls `prog(0)`, and `prog` requires `x@ > 0`; Creusot admits no program function in a logic body at all.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-119: `creusot_test::caller verified ✓` beside `prog verified ✓`.
//@ fixed-by: D-136
//@ also-verified: prog
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use crate::prog as p;

#[requires(x@ > 0)]
#[ensures(result == x)]
pub fn prog(x: i32) -> i32 {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: i32) -> i32 {
    p(y)
}
