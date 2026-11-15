//@ expect: reject
//@ mechanism: the contract-clause spelling of logic_fn_body_view_call_renamed: `use crate::succ as view;` then `view(x@)` in a program function's `ensures`. rustc resolves the clause's call to `succ` in the clause's type-check closure; the contract parser reads the spelling `view(e)` as the view builtin, so the clause was `x@ == x@`. A clause is read as text and no pass settles its calls, so a specification call rustc resolves to a definition its spelling does not name refuses the crate (D-136). Found probing sideways from D-120.
//@ accept-means: a program function is credited on a postcondition that holds only when a renamed call is read as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `view(x@)` is `succ(x@)`, which is `x@ + 1`, never `x@`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::prog verified ✓`. The control is program_ensures_view_call_renamed_control.rs.
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

#[ensures(view(x@) == x@)]
pub fn prog(x: u32) {}
