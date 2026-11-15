//@ expect: reject
//@ mechanism: the method spelling of logic_fn_callee_precondition_use_alias.rs: an inherent logic METHOD's body calls `np(y)` under `use crate::needs_pos as np;`, and `needs_pos` requires `x > 0`. With D-120 open the callee-precondition walk read the call by its spelling, named no definition `np` and owed nothing; with D-136 it owes the precondition of the definition rustc resolved the call to, in a method's body as in a free function's.
//@ accept-means: a logic method that calls another function outside its precondition, through a renaming import, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0`, `S.m(0)` calls `needs_pos(0)`, which requires `x > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `trust-wp: creusot_test::S::m verified ✓`; FAILED (logic callee precondition) with D-136. The control is logic_fn_callee_precondition_use_alias_in_inherent_method_control.rs, which differs in the method's `requires` alone and verifies with D-136.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

use crate::needs_pos as np;

pub struct S;

impl S {
    #[logic(open)]
    #[ensures(true)]
    pub fn m(self, y: Int) -> Int {
        np(y)
    }
}
