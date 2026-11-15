//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_ufcs_trait_method, differing in the caller's `#[requires(y > 0)]` alone: the qualified call must be owed as the trait method's and discharged, not refused.
//@ accept-means: n/a (control) — every argument the caller admits is inside `m`'s precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[requires(x > 0)]
    fn m(x: Int) -> Int;
}

pub struct S;

impl Tr for S {
    #[logic(open)]
    #[requires(x > 0)]
    fn m(x: Int) -> Int {
        x
    }
}

#[logic]
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    <S as Tr>::m(y)
}
