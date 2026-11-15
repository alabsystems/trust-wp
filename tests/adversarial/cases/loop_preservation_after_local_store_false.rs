//@ expect: reject
//@ mechanism: reject twin of loop_preservation_after_local_store_control: the same store before the
//@ mechanism: loop, and an invariant `i <= 2u32` that the third iteration breaks whatever `k` holds.
//@ mechanism: No premise links `k` to `i`, so the model is a run of the program and the refutation
//@ mechanism: stands: withholding every refutation beside a pre-loop store would lose it.
//@ accept-means: `f` runs `i` up to 3, so `i <= 2u32` is FALSE after the third iteration, and
//@ accept-means: trust-wp proved it preserved.
//@ verdict: failed
//@ fn-failed: f
//@ teeth: not a false-accept gate: refuted `failed` before and since D-225. It pins the flavour:
//@ teeth: it was `unknown` on a build that withheld every refutation beside a
//@ teeth: pre-loop store.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let mut k = 0u32;
    let r = &mut k;
    *r = 5;
    let mut i = 0u32;
    #[invariant(i <= 2u32)]
    while i < 3 { i += 1; }
}
