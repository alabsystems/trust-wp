//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_use_alias, differing in the caller's `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so a fix that resolves the renamed call must still verify it.
//@ accept-means: n/a (control) — the call through the renaming import is inside the callee's precondition wherever the caller may be called.
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
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    np(y)
}
