//@ expect: reject
//@ mechanism: the trait-method spelling of program_ensures_view_call_renamed: `use crate::succ as view;` then `view(result@)` in a trait method's `ensures` and in its implementation's. rustc resolves both calls to `succ`; the contract parser reads the spelling as the view builtin, so the clauses were `result@ == result@`. Every specification's type-check closure is read against its text, a trait's and an impl's alike, so the crate is refused (D-136). Found probing sideways from D-120.
//@ accept-means: an implementation is credited on a postcondition that holds only when a renamed call is read as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `view(result@)` is `succ(result@)`, which is `result@ + 1`, never `result@`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `<S as T>::get verified ✓`. The control is program_trait_method_ensures_view_call_renamed_control.rs.
//@ fixed-by: D-136
//@ verdict: error
//@ refused-with: a call `view(..)` in a specification that rustc resolves to `succ`, which the contract parser reads as the `view` builtin
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn succ(x: Int) -> Int {
    x + 1
}

use crate::succ as view;

pub trait T {
    #[ensures(view(result@) == result@)]
    fn get(&self) -> u32;
}

pub struct S;

impl T for S {
    #[ensures(view(result@) == result@)]
    fn get(&self) -> u32 {
        0
    }
}
