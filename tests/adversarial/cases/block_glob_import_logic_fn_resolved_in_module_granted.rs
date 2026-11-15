//@ expect: reject
//@ mechanism: a glob `use crate::other::*;` declared in a block brings `other::k` (0) into the block;
//@ mechanism: the crate root declares another `k` (10). A glob in an inner scope shadows an item of an
//@ mechanism: outer one, so Rust resolves `k()` in the contract of `inner`, declared in the block, to
//@ mechanism: `other::k`. The resolver looks `k` up among the children of the owner's MODULE and reads
//@ mechanism: the root's `k`, and `inner`, which returns 10, is verified against a contract it
//@ mechanism: violates. The glob spelling of block_local_logic_fn_name_resolved_in_module_granted.rs.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: the block's glob
//@ fixed-by: brings `other::k` (0), which shadows the root's, and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == k()` with the glob-imported `other::k` (0) and returns 10,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`). With D-195: `host::inner FAILED ✗
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

pub mod other {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
}

pub fn host() -> u32 {
    #[allow(unused_imports)]
    use crate::other::*;
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        10
    }
    inner()
}
