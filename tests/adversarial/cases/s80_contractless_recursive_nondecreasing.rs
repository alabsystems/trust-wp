//@ expect: reject
//@ mechanism: a LOCAL contract-less RECURSIVE callee must still owe its termination obligation after the empty self-spec is injected
//@ accept-means: route (a)'s empty self-spec injection (extraction.rs:421-422) swallowed the variant-decrease obligation — `rec_up(n+1)` under `#[variant(n)]` does not decrease, so `rec_up(1)` never returns
//@ fixed-by: n/a — s80 FALSE-ACCEPT gate for the route the front actually took
//@ verdict: failed
//@ fn-failed: rec_up
//@ teeth: this is the direct blast radius of route (a) — the ONLY shape whose self-call resolution the fix changes. Rejected before (via `requires(false)`) and after (via the variant-decrease obligation); the A/B that matters is that the REASON changed from a fabricated `ensures` to the real variant goal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// Empty requires AND empty ensures — exactly the shape whose self-spec route (a)
// starts injecting. WRONG: `n + 1` does not decrease, so `rec_up(1)` diverges.
#[check(terminates)]
#[variant(n)]
pub fn rec_up(n: i32) -> i32 {
    if n <= 0 { 0 } else { rec_up(n + 1) }
}
