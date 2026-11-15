//@ expect: reject
//@ mechanism: the fn-item-binding spelling of logic_fn_std_unwrap_logic_precondition: `let u = Option::unwrap_logic; u(o)`. The walk states Creusot's `unwrap_logic` precondition for a call SPELLED `unwrap_logic` (`std_logic_precondition`); `u(o)` is spelled `u`, so nothing owes `o != None`. Found probing sideways from D-120.
//@ accept-means: a logic function that unwraps a possibly-`None` option, through a local the function is bound to, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `o == None` the body evaluates `Option::unwrap_logic(None)`; Creusot's `vc_caller` owes `o != None` and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(true)]
pub fn caller(o: Option<Int>) -> Int {
    let u = Option::unwrap_logic;
    u(o)
}
