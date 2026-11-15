//@ expect: reject
//@ mechanism: a generic `F: Fn` value forwarded by a LOCAL hop to `Option::map`. The caller hands
//@ mechanism: its closure to a body trust-wp verifies (`apply`), so nothing is owed at the caller;
//@ mechanism: `apply` hands `F` to a combinator that calls it under no precondition, and `F`'s
//@ mechanism: precondition is unknown there. `apply` states none (Creusot refutes it on
//@ mechanism: `Option::map`'s `f.precondition`), so `apply` is refused.
//@ accept-means: `apply` is reported `verified` although `apply(Some(0), |j| w[j])` with an empty
//@ accept-means: `w` panics inside the closure `Option::map` runs.
//@ fixed-by: D-118
//@ teeth: ACCEPTED (exit 0, `apply verified`, `pick verified`) on the binary before D-118.
//@ teeth: `pick` stays credited after it, and truly: its one call meets `apply`'s contract, and the
//@ teeth: panic is `apply`'s, whose credit is withdrawn.
//@ also-verified: anchor, pick
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// FALSE as a verified program function: `F`'s precondition is unknown here.
#[requires(true)]
pub fn apply<F: Fn(usize) -> u32>(o: Option<usize>, f: F) -> Option<u32> {
    o.map(f)
}

#[ensures(result@ == 1)]
pub fn pick(w: &[u32]) -> u32 {
    let _ = apply(Some(0), |j| w[j]);
    1
}
