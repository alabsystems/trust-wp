//@ expect: reject
//@ mechanism: map_inv collect view facts — function-level facts about a per-call-site symbol must not fix a loop-varying range bound
//@ fixed-by: wp-s24 (collect-hardening-v2)
//@ accept-means: a collect fact from one loop iteration (k == 1) was applied to the value collected on the last iteration. Refuting execution: the loop runs twice, the last collect uses k == 2, so result@.len() == 2, not 1.
//@ teeth: UNVERIFIED as a defect detector — on wp-s24 it ends FAILED (postcondition); guards against site facts that capture loop-varying bounds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// FALSE: after the loop, out was collected with k == 2, so len == 2.
#[ensures(result@.len() == 1)]
pub fn lp() -> Vec<u32> {
    let mut k: u32 = 1;
    let mut out: Vec<u32> = Vec::new();
    let mut i: u32 = 0;
    #[invariant(i@ <= 2)]
    #[invariant(k@ == i@ + 1)]
    while i < 2 {
        out = (0u32..k).map_inv(|x, _| x).collect();
        k += 1;
        i += 1;
    }
    out
}
