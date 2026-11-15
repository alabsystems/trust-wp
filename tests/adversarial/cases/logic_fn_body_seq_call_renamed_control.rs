//@ expect: verify
//@ xfail: an encoder gap the rename does not touch: the same claim of `pair(y)` called by its own name, with no rename, is demoted on `panic_recovery_false(2)` too, and a claim of the literal's length is refuted, true as it is. The rename is proved read as its callee by logic_fn_body_seq_call_renamed_scalar_callee_control.rs.
//@ mechanism: control for logic_fn_body_seq_call_renamed, differing in the claim alone: `result == pair(y)` holds only if the renamed call is read as `pair`, not as the one-element literal.
//@ accept-means: n/a (control) — `caller(y)` is `pair(y)`.
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
#[ensures(result == pair(y))]
pub fn caller(y: Int) -> Seq<Int> {
    seq(y)
}
