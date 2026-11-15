//@ expect: reject
//@ mechanism: the loop condition calls a function whose trusted contract is `ensures(false)`. The
//@ mechanism: invariant is owed at loop entry, BEFORE the condition is evaluated, so the condition's
//@ mechanism: clauses belong to the VCs that assume the condition or its negation and never to
//@ mechanism: initialization: stated there, `false` discharges the entry obligation.
//@ accept-means: `e(0)` reaches the loop with `i == 5`, so `invariant(i == 0u32)` is FALSE at entry,
//@ accept-means: and trust-wp proved it.
//@ teeth: UNVERIFIED as a false-accept gate: `e FAILED (loop invariant)` at initialization
//@ teeth: before and since D-222. Since D-222 preservation, which does assume the condition, is
//@ teeth: reported vacuous (`unknown`), which is how a regression stating it at entry would read.
//@ verdict: failed
//@ fn-failed: e
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(false)]
pub fn stop(k: u32) -> bool { k > 0 }

pub fn e(n: u32) {
    let mut i = 5u32;
    #[invariant(i == 0u32)]
    while stop(i) { i = 0; }
}
