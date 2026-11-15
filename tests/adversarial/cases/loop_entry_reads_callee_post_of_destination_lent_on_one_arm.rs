//@ expect: reject
//@ mechanism: `let mut m = one(); if c { set5(&mut m); }` before an annotated loop whose invariant reads
//@ mechanism: `m == 1u32`. The block-slice walker named `one`'s result by the destination's bare name `m`, and
//@ mechanism: the postcondition `m == 1` it states for the code before the loops became a premise of the
//@ mechanism: loop's initiation, where `m` is the value the arm's loan left.
//@ accept-means: an invariant is initiated from a callee's postcondition about a value the local no longer
//@ accept-means: holds at the loop's entry, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(n, true)` enters the loop with `m == 5`.
//@ also-verified: one, set5
//@ fixed-by: D-243 (f): a call whose destination may change again before a loop is entered names its result
//@ fixed-by: by a symbol of its site (`PastLoopNames::changed_again_before_the_loops`), never by the bare name.
//@ teeth: ACCEPTED at exit 0 before D-243; `unknown` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn one() -> u32 {
    1
}

#[ensures(^x == 5u32)]
pub fn set5(x: &mut u32) {
    *x = 5;
}

#[requires(n < 10u32)]
pub fn f(n: u32, c: bool) {
    let mut m = one();
    if c {
        set5(&mut m);
    }
    let mut i = 0u32;
    #[invariant(m == 1u32)]
    while i < n {
        i += 1;
    }
}
