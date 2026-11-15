//@ expect: verify
//@ mechanism: stale by-value local after a field write — over-refusal control
//@ fixed-by: s34 functional update of by-value locals on projected writes
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_byval_local_tuple with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result.0 == 5u64 && result.1 == 2u64)]
pub fn local_tuple() -> (u64, u64) {
    let mut p = (1u64, 2u64);
    p.0 = 5;
    p
}
