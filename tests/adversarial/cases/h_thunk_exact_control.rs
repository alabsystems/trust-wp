//@ expect: verify
//@ mechanism: exact-thunk rule — over-refusal control: a capture-free, parameter-free literal thunk is exact and must keep verifying.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: n/a (control) — this contract is TRUE
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn map_or_else_literal() {
    let none: Option<i32> = None;
    let r = none.map_or_else(|| 2, |x| x);
    proof_assert!(r == 2i32);
}
