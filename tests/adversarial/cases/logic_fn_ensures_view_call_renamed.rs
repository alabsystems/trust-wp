//@ expect: reject
//@ mechanism: the logic-contract spelling of program_ensures_view_call_renamed: the renamed `view(y)` is in a logic function's `ensures`, not its body, and was read as the view builtin. A logic function's contract is a specification like a program function's, and the call refuses the crate (D-136). Found probing sideways from D-120.
//@ accept-means: a logic function is credited on a postcondition that holds only when a renamed call is read as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `view(y)` is `succ(y)`, which is `y + 1`, never `y`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`.
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

#[logic]
#[ensures(view(y) == y)]
pub fn caller(y: Int) -> Int {
    y
}
