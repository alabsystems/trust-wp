//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_alias_in_macro_generated_fn, differing in the generated function's `#[requires(y > 0)]` alone: every argument it admits is inside `needs_pos`'s precondition.
//@ accept-means: n/a (control) — the renamed call in the generated body is inside the callee's precondition wherever the function may be called.
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
        #[requires(y > 0)]
        #[ensures(true)]
        pub fn $name(y: Int) -> Int {
            np(y)
        }
    };
}

mk!(caller);
