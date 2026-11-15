//@ expect: reject
//@ mechanism: the local-definition spelling of logic_fn_body_view_call_renamed, with no rename at all: a module defines its own logic function `view` and calls it as `view(y)`. rustc resolves the call to `m::view`, which shadows the prelude's glob-imported `view`; the contract parser reads `view(e)` as the view builtin, so the ensures lane proves `result == y` of a body that is `y + 1`. Found probing sideways from D-120.
//@ accept-means: a logic function calling a local function named `view` is credited with the builtin view's postcondition, and the crate exits 0.
//@ WHY IT IS FALSE: `m::caller(y)` is `m::view(y)`, which is `y + 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::m::caller verified ✓`. The control is logic_fn_body_view_call_local_fn_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    use creusot_std::prelude::*;

    #[logic]
    pub fn view(x: Int) -> Int {
        x + 1
    }

    #[logic]
    #[ensures(result == y)]
    pub fn caller(y: Int) -> Int {
        view(y)
    }
}
