//@ expect: reject
//@ mechanism: a loop-body call whose precondition reads only the loop counter, beside a store through
//@ mechanism: `a` before the loop: no premise links `i` to `*a`, so the model with `i == 2` is a
//@ mechanism: run of the program and the refutation stands. A rule that withheld every group
//@ mechanism: refutation in a function with a pre-loop store would lose it.
//@ accept-means: `f` calls `small(2)` on its third iteration, violating `x@ < 2`, and trust-wp proved
//@ accept-means: the call.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: small
//@ teeth: not a false-accept gate: refuted `failed` before and since D-225; it pins the flavour
//@ teeth: against a stale-store rule that over-withholds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 2)]
pub fn small(x: u32) {}

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { small(i); i += 1; }
}
