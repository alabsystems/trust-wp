//@ expect: reject
//@ mechanism: lane-choice control for s61_variant_lane_pa_false — the SAME false assertion with `#[variant]` REMOVED. The function then carries no clauses at all, the standalone proof_assert pass owns it (standalone_proof_assert.rs skips only functions that DO carry clauses), and the assertion is examined on the campaign build too.
//@ accept-means: the standalone fallback lane stopped examining clause-free functions.
//@ fixed-by: n/a — must be rejected before AND after wp-s61.
//@ teeth: n/a by construction — rejected on wp-campaign 04fc8074 as well; the point is that adding `#[variant(n)]` to this exact body made it ACCEPT there.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn countdown4(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        proof_assert!(false);
        countdown4(n - 1)
    }
}
