//@ expect: verify
//@ mechanism: stale by-value local after a field write — over-refusal control
//@ fixed-by: s34 functional update of by-value locals on projected writes
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_byval_local_struct with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u64,
    pub b: u64,
}

#[ensures(result.a == 5u64 && result.b == 2u64)]
pub fn local_struct() -> P {
    let mut p = P { a: 1, b: 2 };
    p.a = 5;
    p
}
