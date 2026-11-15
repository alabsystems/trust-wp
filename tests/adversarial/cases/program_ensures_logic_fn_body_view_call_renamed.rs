//@ expect: reject
//@ mechanism: the program spelling of logic_fn_body_view_call_renamed_through_uncontracted_callee: a program function's `ensures` names the logic function `wrapper`, whose body is a renamed `view(y)`. The program lane reads `wrapper`'s defining axiom as the parser left it, `y@`, and proves `wrapper(x@) == x@`. Found probing sideways from D-120.
//@ accept-means: a program function is credited on a postcondition about a logic function whose definition reads a renamed call as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `wrapper(x@)` is `succ(x@)`, which is `x@ + 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::prog verified ✓`. The control is program_ensures_logic_fn_body_view_call_renamed_control.rs.
//@ fixed-by: D-136
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

#[ensures(wrapper(x@) == x@)]
pub fn prog(x: u32) {}
