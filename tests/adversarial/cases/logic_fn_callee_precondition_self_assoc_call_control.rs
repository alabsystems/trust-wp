//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_self_assoc_call, differing in the caller's `#[requires(y > 0)]` alone.
//@ accept-means: n/a (control) — every argument the caller admits is inside `helper`'s precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;

impl S {
    #[logic]
    #[requires(x > 0)]
    pub fn helper(x: Int) -> Int {
        x
    }

    #[logic]
    #[requires(y > 0)]
    #[ensures(true)]
    pub fn caller(y: Int) -> Int {
        Self::helper(y)
    }
}
