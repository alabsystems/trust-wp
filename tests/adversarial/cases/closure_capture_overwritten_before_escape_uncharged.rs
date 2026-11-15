//@ expect: reject
//@ mechanism: an escaping closure reads a capture the host OVERWROTE after entry. The host's
//@ mechanism: `requires` speaks of `k` at entry; the closure captures `k` after `k = 100`. A closure
//@ mechanism: target that inherited the host's entry facts for its captures (the D-106 environment
//@ mechanism: defect, through the obligation lane instead of the assertion lane) would read
//@ mechanism: `k < w.len()` and discharge the bounds check.
//@ accept-means: `pick` is reported `verified` although `pick(Some(1), &[7], 0)` indexes `w[100]`
//@ accept-means: inside the closure `Option::map` runs.
//@ WHY THE CONTRACT IS FALSE: `k` is 100 when the closure is built, and `w` may be shorter.
//@ fixed-by: D-118: the escaping closure is verified under `requires true`, every capture at any
//@ fixed-by: value its type allows, and `pick` rests on that verdict.
//@ teeth: ACCEPTED, exit 0, `pick verified`, on the binary before D-118. After it the closure is not
//@ teeth: verified and `pick`'s credit is withdrawn.
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

// FALSE: `pick(Some(1), &[7], 0)` indexes `w[100]`.
#[requires(k@ < w@.len())]
#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>, w: &[u32], mut k: usize) -> u32 {
    k = 100;
    let _ = o.map(|_x| w[k]);
    1
}
