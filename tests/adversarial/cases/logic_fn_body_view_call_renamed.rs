//@ expect: reject
//@ mechanism: `use crate::succ as view;` then `view(y)` in a logic body. rustc resolves the call to `succ`, and so does Creusot, whose Pearlite leaves `view(..)` to rustc. The contract parser reads the spelling `view(e)` as the view of `e` (`call_or_reference_form`), so the body is `y@`, which for an `Int` is `y`, and the ensures lane proves `result == y`. The callee-precondition walk sees the type-checked call but owes nothing, since `succ` has no `requires`. Found probing sideways from D-120.
//@ accept-means: a logic function whose body calls a function renamed onto the spelling `view` is credited with a postcondition that holds only of the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `caller(y)` is `succ(y)`, which is `y + 1`, never `y`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_body_view_call_renamed_control.rs.
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
#[ensures(result == y)]
pub fn caller(y: Int) -> Int {
    view(y)
}
