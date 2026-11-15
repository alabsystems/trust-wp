//@ expect: verify
//@ xfail: unwrap_or_else(|| 3) gets no postcondition fact at all and ok_or_else's Err payload projection (tuple_get_0 of Err) is quantifier-unhandled; both were unknown identically BEFORE wp-s23 (A/B on the 0989c2e driver), so this is a pre-existing encoding gap, not an over-refusal of the exact-thunk rule
//@ mechanism: exact-thunk rule — true literal thunk contracts that should verify once the unrelated Option/Result encoding gaps close.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: n/a (control) — these contracts are TRUE
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn unwrap_or_else_literal() {
    let none: Option<i32> = None;
    let r = none.unwrap_or_else(|| 3);
    proof_assert!(r == 3i32);
}

pub fn ok_or_else_literal() {
    let none: Option<i32> = None;
    let r = none.ok_or_else(|| true);
    if let Err(e) = r {
        proof_assert!(e);
    }
}
