//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_alias_under_quantifier, differing in the guard `z > 0 ==>` alone: the renamed call is reached only where its argument is positive, so it must be owed as `needs_pos`'s under the binder and the guard, and discharged, not refused.
//@ accept-means: n/a (control) — the renamed call is inside the callee's precondition for every value of the binder that reaches it.
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
    pearlite! { forall<z: Int> z > 0 ==> np(z) == z }
}
