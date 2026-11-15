//@ expect: reject
//@ mechanism: the contract-clause spelling of logic_fn_body_some_call_renamed: `use crate::nothing as Some;` then `Some(x@)` in a program function's `ensures`, which the encoder read as the `Option` constructor. A specification call rustc resolves to a definition its spelling does not name refuses the crate (D-136). Found probing sideways from D-120.
//@ accept-means: a program function is credited on a postcondition that holds only when a renamed call is read as a constructor, and the crate exits 0.
//@ WHY IT IS FALSE: `Some(x@)` is `nothing(x@)`, which is `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::prog verified ✓`.
//@ fixed-by: D-136
//@ verdict: error
//@ refused-with: a call spelled `Some` in a specification that rustc resolves to `nothing`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn nothing(x: Int) -> Option<Int> {
    None
}

use crate::nothing as Some;

#[ensures(Some(x@) != None)]
pub fn prog(x: u32) {}
