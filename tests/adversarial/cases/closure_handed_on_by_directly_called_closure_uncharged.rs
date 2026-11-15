//@ expect: reject
//@ mechanism: a host CALLS a contract-free closure of its own, and that closure hands another closure
//@ mechanism: to `Option::map`. The call is charged the called closure's precondition, its body's WP
//@ mechanism: (D-54), and that WP reads `Option::map` as owing nothing. The called closure escapes
//@ mechanism: nowhere; the host's own body hands nothing to unverified code.
//@ accept-means: `pick` is reported `verified` although `pick(Some(0), &[])` indexes an empty slice
//@ accept-means: inside the closure `Option::map` runs.
//@ fixed-by: D-118: a host rests on the hand-offs of every closure it defines, as on its own.
//@ teeth: ACCEPTED, exit 0, `pick verified`, on the binary before D-118. After it the inner closure
//@ teeth: is a target that is not verified, and `pick` is withdrawn through the closure it defines
//@ teeth: and calls.
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
    let run = |p: Option<usize>| {
        let _ = p.map(|j| w[j]);
    };
    run(o);
    1
}
