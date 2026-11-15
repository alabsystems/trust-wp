//@ expect: reject
//@ mechanism: the same field-order confusion in a loop `#[invariant]`. Both variant fields are
//@ mechanism: u32, so this is a VALUE confusion: the invariant is written about `b` and read
//@ mechanism: positionally (source order `{b, a}`) about `a`, which the precondition supplies.
//@ accept-means: a loop invariant that cannot be established is reported as proved because it
//@ accept-means: silently attached to a different field than the one named.
//@ WHY THE CONTRACT IS FALSE: the invariant asserts `b == 5`; `f(Q2::C { a: 5, b: 0 })` enters
//@ WHY THE CONTRACT IS FALSE: the loop with `b == 0`, so it never holds on entry.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub enum Q2 { C { a: u32, b: u32 }, N }
#[requires(match q { Q2::C { a: aa, b: _b } => aa@ == 5, Q2::N => true })]
pub fn f(q: Q2) {
    let mut i: u32 = 0;
    #[invariant(match q { Q2::C { b: bb, a: _a } => bb@ == 5, Q2::N => true })]
    while i < 3 { i += 1; }
}
