//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_method_call, differing in the caller's `#[requires]` alone: the receiver it admits satisfies the method's precondition.
//@ accept-means: n/a (control) — the call is inside the method's precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub v: i32,
}

impl S {
    #[logic]
    #[requires(self.v@ > 0)]
    pub fn m(self) -> Int {
        pearlite! { self.v@ }
    }
}

#[logic]
#[requires(s.v@ > 0)]
#[ensures(true)]
pub fn caller(s: S) -> Int {
    s.m()
}
