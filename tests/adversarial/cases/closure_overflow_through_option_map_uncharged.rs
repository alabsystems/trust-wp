//@ expect: reject
//@ mechanism: the arithmetic sibling of closure_index_through_option_map_uncharged. A closure whose
//@ mechanism: only obligation is an overflow check is handed to `Option::map`. Before D-118 the
//@ mechanism: closure was already its own target through the arithmetic discovery and was refuted,
//@ mechanism: but the contracted host kept its credit: nothing tied the host to the verdict of the
//@ mechanism: closure it handed over, so the run failed while the per-function claim on `pick` stood.
//@ accept-means: `pick` is reported `verified` although `pick(Some(u32::MAX))` overflows inside the
//@ accept-means: closure `Option::map` runs.
//@ WHY THE CONTRACT IS FALSE: `pick(Some(u32::MAX))` panics before it returns.
//@ fixed-by: D-118: the host rests on the verdict of every closure it hands to code trust-wp does
//@ fixed-by: not verify.
//@ teeth: on the binary before D-118, `pick verified` beside `pick::{closure#1} FAILED`, a credit the
//@ teeth: per-function gate flags. After it `pick`'s credit is withdrawn.
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

// FALSE: `pick(Some(u32::MAX))` overflows.
#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>) -> u32 {
    let _ = o.map(|x| x + 1);
    1
}
