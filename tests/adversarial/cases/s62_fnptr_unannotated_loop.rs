//@ expect: reject
//@ mechanism: a fn-pointer call inside a loop carrying NO #[invariant] owes its target's precondition
//@ fixed-by: s62 (wp-s62, shared loop-call-target classification)
//@ accept-means: the unannotated-loop lane dropped the whole call handler for a non-FnDef callee, so `needs_positive(0)` — `0 > 0` — was never owed.
//@ verdict: failed
//@ fn-failed: evil
//@ teeth: verified ✓ (exit 0) on wp-campaign 04fc8074 (debug driver); FAILED ✗ on wp-s62.
//@ also-verified: needs_positive
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x > 0u32)]
#[ensures(result == x)]
pub fn needs_positive(x: u32) -> u32 {
    x
}

// The callee's precondition `0 > 0` is violated on every run.
#[ensures(result == 7u32)]
pub fn evil() -> u32 {
    let f: fn(u32) -> u32 = needs_positive;
    let mut i = 0u32;
    while i < 1u32 {
        let _unused = f(0u32);
        i += 1u32;
    }
    7u32
}
