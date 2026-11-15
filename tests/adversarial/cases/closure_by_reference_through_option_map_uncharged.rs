//@ expect: reject
//@ mechanism: the closure of closure_index_through_option_map_uncharged bound to a local and handed
//@ mechanism: over BY REFERENCE (`o.map(&c)`, through `impl Fn for &F`). The escape scan reads the
//@ mechanism: callable out of the argument's type, references included; a scan that looked only
//@ mechanism: for a closure-typed argument would miss it.
//@ accept-means: `pick` is reported `verified` although `pick(Some(0), &[])` panics with "index out
//@ accept-means: of bounds".
//@ fixed-by: D-118
//@ teeth: ACCEPTED (exit 0, `pick verified`) on the binary before D-118.
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
    let c = |j: usize| w[j];
    let _ = o.map(&c);
    1
}
