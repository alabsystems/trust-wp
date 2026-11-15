//@ expect: reject
//@ mechanism: `use crate::nothing as Some;` then `Some(y)` in a logic body. rustc resolves the call to `nothing`, which shadows the prelude's `Some`; the identity pass leaves the call spelled (no local definition is named `Some`) and the encoder reads a call spelled `Some` as the `Option` constructor, so the ensures lane proves `result != None` of a body that is `None`. Found probing sideways from D-120.
//@ accept-means: a logic function whose body calls a function renamed onto a constructor's name is credited with the constructor's postcondition, and the crate exits 0.
//@ WHY IT IS FALSE: `caller(y)` is `nothing(y)`, which is `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_body_some_call_renamed_control.rs.
//@ fixed-by: D-136
//@ note: D-136 resolves the call to `nothing` correctly. Before D-165 the solver still proved `result != None` through the Option re-wrap (program_ensures_option_param_returned_read_as_some and its siblings) and a structural refutation check withheld that proof; with D-165 the body is `nothing(y)` read at its own sort and the solver proves nothing (`postcondition unverified (refutation withheld: solver evidence was unknown, not a satisfying counterexample model)`), so the case rests on D-136 alone.
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition unverified
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

#[logic]
#[ensures(result != None)]
pub fn caller(y: Int) -> Option<Int> {
    Some(y)
}
