//@ expect: reject
//@ mechanism: map_inv collect view facts — facts about the b-branch collect must not constrain the Vec::new branch sharing the return slot
//@ fixed-by: wp-s24 (collect-hardening-v2, v3)
//@ accept-means: map_inv facts about the shared return slot made the else branch contradictory. Refuting execution: b = false returns Vec::new(), length 0, not 7.
//@ teeth: Review of 51cca4a (probe p9): vacuous via call_0 sharing. Asserts a clean refutation from ay.
//@ verdict: failed
//@ fn-failed: vac
//@ ay-not-unsat: vac
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// FALSE: b == false returns an EMPTY Vec.
#[ensures(result@.len() == 7)]
pub fn vac(b: bool) -> Vec<u32> {
    if b {
        (0u32..3).map_inv(|x, _| x).collect()
    } else {
        Vec::new()
    }
}
