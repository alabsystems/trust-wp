//@ expect: reject
//@ mechanism: a logic body calls a trait's logic method by its fully qualified path, `<S as Tr>::m(y)`, and the trait method and its implementation require `x > 0`. rustc names the trait method and resolves the implementation that runs; the walk owes the precondition of every definition rustc resolves the call to (D-136). Pins the qualified-path spelling the resolution record reads. Found probing sideways from D-120.
//@ accept-means: a logic function that calls a trait's logic method outside its precondition, through a qualified path, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `<S as Tr>::m(0)`, and `m` requires `x > 0`.
//@ teeth: UNVERIFIED, a shape gate: rejected with D-120 open too, since the spelling `m` names the contracted trait method and D-119 item 2 owes what a spelling names; with D-136 it FAILS on the callee precondition through the resolution as well. The control is logic_fn_callee_precondition_ufcs_trait_method_control.rs.
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
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    <S as Tr>::m(y)
}
