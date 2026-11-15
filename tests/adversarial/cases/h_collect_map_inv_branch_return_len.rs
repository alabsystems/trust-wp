//@ expect: reject
//@ mechanism: map_inv collect view facts — must be about a per-call-site symbol, never about call_<dest> shared across paths
//@ fixed-by: wp-s24 (collect-hardening-v2)
//@ accept-means: map_inv facts about the shared return slot constrained the else branch. Refuting execution: b = false returns Vec::new(), length 0, not 3.
//@ teeth: Review of 51cca4a: vacuous (contradictory premises) via call_0 sharing; must now be a clean FAILED (postcondition).
//@ verdict: failed
//@ fn-failed: branch
//@ ay-not-unsat: branch
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// b == false returns an EMPTY Vec; the ensures is false.
#[ensures(result@.len() == 3)]
pub fn branch(b: bool) -> Vec<u32> {
    if b {
        (0u32..3).map_inv(|x, _| x).collect()
    } else {
        Vec::new()
    }
}
