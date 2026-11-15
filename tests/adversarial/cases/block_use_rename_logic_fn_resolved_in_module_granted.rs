//@ expect: reject
//@ mechanism: a `use ... as k` declared in a block binds `k` to `other::zero` (0); the crate root
//@ mechanism: declares a logic function `k` (10), the only local one of that name. Rust resolves `k()`
//@ mechanism: in the contract of `inner`, declared in the block, through the renamed import. The
//@ mechanism: resolver looks `k` up among the children of the owner's MODULE, finds the root's `k`, and
//@ mechanism: `inner`, which returns 10, is verified against a contract it violates. The renaming
//@ mechanism: spelling of block_local_logic_fn_name_resolved_in_module_granted.rs.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: the block's renamed
//@ fixed-by: import binds `k` to `other::zero` (0), and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == k()` with `k` bound to `other::zero` (0) and returns 10,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`). With D-195: `host::inner FAILED ✗
//@ teeth: (postcondition)`.
//@ teeth: With D-136's refusal of a renamed call in force beside D-195, the crate is refused
//@ teeth: before either reading is used: the call's spelling `k` is not the name of the item rustc
//@ teeth: resolves it to.
//@ verdict: error
//@ refused-with: a call spelled `k` in a specification that rustc resolves to `other::zero`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub mod other {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn zero() -> Int {
        pearlite! { 0 }
    }
}

pub fn host() -> u32 {
    use crate::other::zero as k;
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        10
    }
    inner()
}
