//@ expect: reject
//@ mechanism: inline_const_closure_index_through_option_map_uncharged with the indexing moved one
//@ mechanism: const deeper: the closure `Option::map` runs is written in an inline `const { }` and
//@ mechanism: calls a closure written in a `const { }` inside it. The outer closure was examined and
//@ mechanism: refuted on the inner one's bounds check, but the escape scan never recorded the hand-off
//@ mechanism: (its owner walk stopped at the const), so `pick` rested on no verdict and kept its credit.
//@ accept-means: `pick` is reported `verified` although `pick(Some(5), 0)` panics with "index out
//@ accept-means: of bounds".
//@ WHY THE CONTRACT IS FALSE: `pick(Some(5), 0)` runs `[1u32, 2][5]`.
//@ fixed-by: D-123: a closure's owner walk goes out through every inline or anonymous const.
//@ teeth: MEASURED on the binary before D-123: `pick::{constant#0}::{closure#0} FAILED` and
//@ teeth: `pick verified ✓`. After it `pick` is withdrawn: it hands that closure to `Option::map`
//@ teeth: and the closure was not verified.
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

#[ensures(result@ == k@)]
pub fn pick(o: Option<usize>, k: u32) -> u32 {
    let _ = o.map(const { |j: usize| (const { |i: usize| [1u32, 2][i] })(j) });
    k
}
