//@ expect: reject
//@ mechanism: the method-call spelling of logic_fn_callee_precondition_generic_trait_method_ufcs: `t.m(y)` on `t: T` with `T: Tr`, whose logic method requires `x > 0`. rustc resolves a method call through the body's typeck results (`type_dependent_def`), so the walk owes the trait method's precondition (D-136). Found probing sideways from D-120.
//@ accept-means: a generic logic function that calls a trait's logic method outside its precondition, as a method, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `t.m(0)`, and `Tr::m` requires `x > 0`.
//@ teeth: UNVERIFIED, a shape gate: rejected with D-120 open too, since the spelling `m` names the contracted trait method and D-119 item 2 owes what a spelling names; with D-136 it FAILS on the callee precondition through the resolution as well.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[requires(x > 0)]
    fn m(self, x: Int) -> Int;
}

#[logic]
#[ensures(true)]
pub fn caller<T: Tr>(t: T, y: Int) -> Int {
    t.m(y)
}
