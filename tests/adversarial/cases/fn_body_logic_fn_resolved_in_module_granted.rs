//@ expect: reject
//@ mechanism: `inner`'s own body declares a logic function `k` (0) and the crate root declares another
//@ mechanism: (10). Creusot expands a contract clause into an item placed as the FIRST statement of the
//@ mechanism: function's body, and trust-wp's type-check vehicle puts the clause there too, so the
//@ mechanism: clause is resolved where the body's items are in scope: `k()` means the body's `k`. The
//@ mechanism: resolver looks `k` up among the children of the owner's MODULE and reads the root's `k`,
//@ mechanism: and `inner`, which returns 10, is verified against the contract Creusot gives it, which
//@ mechanism: it violates.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: an item of the
//@ fixed-by: owner's top-level body block answers a `requires`/`ensures`, and `k` is the body's (0),
//@ fixed-by: and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == k()` with its body's `k` (0) and returns 10, and the crate
//@ accept-means: exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`inner verified ✓`). With D-195: `inner FAILED ✗
//@ teeth: (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

#[ensures(result@ == k())]
pub fn inner() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 0 }
    }
    10
}
