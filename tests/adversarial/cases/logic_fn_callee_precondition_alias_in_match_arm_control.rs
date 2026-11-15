//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_alias_in_match_arm, differing in a guard around the call alone: `np(v)` is reached only where `v > 0`, so the renamed call must be owed as `needs_pos`'s under the arm's binding and the guard, and discharged, not refused.
//@ accept-means: n/a (control) — the renamed call is inside the callee's precondition wherever it is evaluated.
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
pub fn caller(o: Option<Int>) -> Int {
    match o {
        Some(v) => {
            if v > 0 {
                np(v)
            } else {
                0
            }
        }
        None => 0,
    }
}
