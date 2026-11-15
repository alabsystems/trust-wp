//@ expect: reject
//@ mechanism: a closure WITH `#[requires]` handed to `Option::map`. The closure's body is verified
//@ mechanism: under its own precondition, but the combinator calls it under none, so the
//@ mechanism: precondition is granted to the body and owed by nobody. Creusot owes it through
//@ mechanism: `Option::map`'s `f.precondition((t,))`; trust-wp's builtin spec states no such
//@ mechanism: requirement, so the host is refused.
//@ accept-means: `pick` is reported `verified` although `pick(Some(0), &[])` panics with "index out
//@ accept-means: of bounds" inside the closure.
//@ fixed-by: D-118
//@ teeth: on the binary before D-118, `pick verified` beside the closure's own refutation, a credit
//@ teeth: the per-function gate flags; after it `pick`'s credit is withdrawn. The closure's body is
//@ teeth: refuted before and after D-118: its `requires` over the captured `w` does not reach the
//@ teeth: bounds check's read of that capture, a completeness gap of the closure lane.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// FALSE: `pick(Some(0), &[])` indexes an empty slice.
#[ensures(result@ == 1)]
pub fn pick(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.map(#[requires(j@ < w@.len())] |j: usize| w[j]);
    1
}
