//@ expect: reject
//@ also-verified: host
//@ mechanism: the closure spelling of block_local_logic_fn_name_resolved_in_module_granted.rs. The
//@ mechanism: closure's contract names `k()`, which Rust resolves to the logic function declared in
//@ mechanism: `host`'s block (0); the crate root declares another `k` (10). The resolver takes the
//@ mechanism: closure's module for its scope, reads the root's `k`, and credits the closure, which
//@ mechanism: returns 10. `host` claims nothing, so its credit is true.
//@ fixed-by: D-174 — the closure is nested in `host`'s body, which declares `k`, so the module's
//@ fixed-by: answer is withheld, `k` names two definitions and the colliding call is refused.
//@ refused-with: names one of several definitions
//@ accept-means: the closure claims `result@ == k()` with the block's `k` (0) and returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::{closure#1} verified ✓`) without D-174's check, before
//@ teeth: D-110 and after it alike; with it, the closure is refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub fn host() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 0 }
    }
    let c = #[ensures(result@ == k())]
    || -> u32 { 10 };
    c()
}
