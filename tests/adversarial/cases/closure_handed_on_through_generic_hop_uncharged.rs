//@ expect: reject
//@ mechanism: a host hands a contract-free closure to a VERIFIED generic hop (`apply` requires
//@ mechanism: `f.precondition(())`), and that closure hands another closure to `Option::map`. The
//@ mechanism: hop is charged the outer closure's precondition, which D-54 reads as its body's WP, and
//@ mechanism: that WP reads `Option::map` as owing nothing, so the host discharges it trivially. The
//@ mechanism: outer closure escapes nowhere and is no target; the inner one escapes and is refuted,
//@ mechanism: but the host handed nothing to unverified code itself.
//@ accept-means: `pick` is reported `verified` although `pick(Some(0), &[])` indexes an empty slice
//@ accept-means: inside the closure `Option::map` runs, two closures below the host.
//@ fixed-by: D-118: a host rests on the hand-offs of every closure it defines, as on its own.
//@ teeth: ACCEPTED, exit 0, `pick verified`, on the binary before D-118, where no closure was
//@ teeth: examined. After it the inner closure is a target that is not verified, and `pick` is
//@ teeth: withdrawn through the closure it defines. `apply`'s credit is TRUE and declared.
//@ also-verified: anchor, apply
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

#[requires(f.precondition(()))]
pub fn apply<F: FnOnce()>(f: F) {
    f()
}

// FALSE: `pick(Some(0), &[])` indexes an empty slice.
#[ensures(result@ == 1)]
pub fn pick(o: Option<usize>, w: &[u32]) -> u32 {
    apply(|| {
        let _ = o.map(|j| w[j]);
    });
    1
}
