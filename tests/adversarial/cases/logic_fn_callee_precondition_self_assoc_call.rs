//@ expect: reject
//@ mechanism: an inherent logic function calls another of its impl as `Self::helper(y)`, and `helper` requires `x > 0`. rustc resolves `Self` to the impl's type and the call to `S::helper`; the walk owes that definition's precondition (D-136). Pins the `Self::` spelling the resolution record reads. Found probing sideways from D-120.
//@ accept-means: an associated logic function that calls another outside its precondition through `Self::` is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `S::caller` calls `S::helper(0)`, and `helper` requires `x > 0`.
//@ teeth: UNVERIFIED, a shape gate: rejected with D-120 open too, since the spelling `helper` names the contracted function and D-119 item 2 owes what a spelling names; with D-136 it FAILS on the callee precondition through the resolution as well. The control is logic_fn_callee_precondition_self_assoc_call_control.rs.
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
    #[ensures(true)]
    pub fn caller(y: Int) -> Int {
        Self::helper(y)
    }
}
