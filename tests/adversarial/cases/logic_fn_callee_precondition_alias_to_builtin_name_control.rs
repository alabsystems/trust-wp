//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_alias_to_builtin_name, differing in the caller's `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so the call renamed onto a builtin's name must be owed as `needs_pos`'s and discharged, not refused.
//@ accept-means: n/a (control) — the renamed call is inside the callee's precondition wherever the caller may be called.
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
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    abs(y)
}
