//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_use_alias_in_inherent_method, differing in the method's `#[requires(y > 0)]` alone: every argument it admits is inside `needs_pos`'s precondition.
//@ accept-means: n/a (control) — the renamed call is inside the callee's precondition wherever the method may be called.
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
    #[requires(y > 0)]
    pub fn m(self, y: Int) -> Int {
        np(y)
    }
}
