//@ expect: reject
//@ mechanism: `use crate::pair as seq;` then `seq(y)` in a logic body. rustc resolves the call to `pair`; the contract parser keeps it as a call named `seq`, the same form as a `seq![..]` literal, the identity pass leaves it spelled (no local definition is named `seq`), and the encoder reads a one-argument `seq` as the one-element sequence (`seq_singleton`). The ensures lane proves `result.len() == 1` of a body that is `seq![y, y]`. Found probing sideways from D-120.
//@ accept-means: a logic function whose body calls a function renamed onto the spelling `seq` is credited with a postcondition of the sequence literal, and the crate exits 0.
//@ WHY IT IS FALSE: `caller(y)` is `pair(y)`, a sequence of length 2.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`. The control is logic_fn_body_seq_call_renamed_control.rs.
//@ fixed-by: D-136
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
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

#[logic]
#[ensures(result.len() == 1)]
pub fn caller(y: Int) -> Seq<Int> {
    seq(y)
}
