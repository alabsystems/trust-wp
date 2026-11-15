//@ expect: reject
//@ mechanism: a `use` declared in a block imports a logic function under a name the crate root also
//@ mechanism: declares. Rust resolves `k()` in the contract of `inner`, declared in the same block,
//@ mechanism: through the block's import (`other::k`, 0): a block's bindings shadow the module's. The
//@ mechanism: resolver looks a bare name up among the children of the owner's MODULE, where the block's
//@ mechanism: import is not, reads the root's `k` (10), and `inner`, which returns 10, is verified
//@ mechanism: against a contract it violates. The import spelling of
//@ mechanism: block_local_logic_fn_name_resolved_in_module_granted.rs.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: the block's import
//@ fixed-by: binds `k` to `other::k` (0), and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == k()` with the imported `other::k` (0) and returns 10, and
//@ accept-means: the crate exits 0.
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
    use crate::other::k;
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        10
    }
    inner()
}
