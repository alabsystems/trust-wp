//@ expect: reject
//@ mechanism: the contract-clause spelling of logic_fn_body_seq_call_renamed: `use crate::pair as seq;` then `seq(x@)` in a program function's `ensures`, which the encoder read as a one-element sequence literal. A specification call rustc resolves to a definition its spelling does not name refuses the crate (D-136). Found probing sideways from D-120.
//@ accept-means: a program function is credited on a postcondition that holds only when a renamed call is read as a sequence literal, and the crate exits 0.
//@ WHY IT IS FALSE: `seq(x@)` is `pair(x@)`, of length 2.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::prog verified ✓`.
//@ fixed-by: D-136
//@ verdict: error
//@ refused-with: a call spelled `seq` in a specification that rustc resolves to `pair`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn pair(x: Int) -> Seq<Int> {
    seq![x, x]
}

use crate::pair as seq;

#[ensures(seq(x@).len() == 1)]
pub fn prog(x: u32) {}
