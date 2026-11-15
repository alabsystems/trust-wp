//@ expect: reject
//@ mechanism: the definition spelling of logic_fn_body_view_call_renamed: the renamed `view(y)` sits in `wrapper`, which has no contract, so no lane of `wrapper`'s own examines its body. The body is still `wrapper`'s defining axiom, read as `y@`, and `caller`'s ensures lane unfolds it. A fix that only withholds the credit of the function whose body is misread leaves every caller reading the misread definition. Found probing sideways from D-120.
//@ accept-means: a logic function is credited through a callee whose defining axiom reads a renamed call as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `caller(y)` is `wrapper(y)`, which is `succ(y)`, which is `y + 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_body_view_call_renamed_through_uncontracted_callee_control.rs.
//@ fixed-by: D-136
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
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

#[logic]
pub fn wrapper(y: Int) -> Int {
    view(y)
}

#[logic]
#[ensures(result == y)]
pub fn caller(y: Int) -> Int {
    wrapper(y)
}
