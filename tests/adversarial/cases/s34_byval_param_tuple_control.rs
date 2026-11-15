//@ expect: verify
//@ mechanism: stale by-value local after a field write — over-refusal control
//@ fixed-by: s34 functional update of by-value locals on projected writes
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_byval_param_tuple with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(t.0 < 100u64)]
#[ensures(result.0 == t.0 + 1u64)]
pub fn param_tuple(mut t: (u64, u64)) -> (u64, u64) {
    t.0 += 1;
    t
}
