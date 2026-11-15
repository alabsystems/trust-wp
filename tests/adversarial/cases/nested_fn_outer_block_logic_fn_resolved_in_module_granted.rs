//@ expect: reject
//@ mechanism: `inner` is declared in the body of `mid`, which is declared in the body of `host`, and
//@ mechanism: `host`'s block declares a logic function `k` (0); the crate root declares another (10).
//@ mechanism: An item sees the items of every block that encloses it, across item boundaries, so Rust
//@ mechanism: resolves `k()` in `inner`'s contract to `host`'s `k`. The resolver looks `k` up among the
//@ mechanism: children of the owner's MODULE, skipping both bodies, reads the root's `k`, and `inner`,
//@ mechanism: which returns 10, is verified against a contract it violates. The nested spelling of
//@ mechanism: block_local_logic_fn_name_resolved_in_module_granted.rs.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: the walk crosses
//@ fixed-by: `mid`'s body to `host`'s block, whose `k` is 0, and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == k()` with `host`'s `k` (0) and returns 10, and the crate
//@ accept-means: exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::mid::inner verified ✓`). With D-195: `host::mid::inner
//@ teeth: FAILED ✗ (postcondition)`.
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
    fn mid() -> u32 {
        #[ensures(result@ == k())]
        fn inner() -> u32 {
            10
        }
        inner()
    }
    mid()
}
