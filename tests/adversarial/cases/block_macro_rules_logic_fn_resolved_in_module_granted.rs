//@ expect: reject
//@ mechanism: a `macro_rules!` invocation in a block declares a logic function `k` (0) there; the crate
//@ mechanism: root declares another `k` (10). `macro_rules!` hygiene does not hide an item's name, so
//@ mechanism: Rust resolves `k()` in the contract of `inner`, declared in the block, to the macro's
//@ mechanism: `k`. The resolver looks `k` up among the children of the owner's MODULE and reads the
//@ mechanism: root's `k`, and `inner`, which returns 10, is verified against a contract it violates.
//@ mechanism: The macro-generated spelling of block_local_logic_fn_name_resolved_in_module_granted.rs.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: the macro's `k` (0)
//@ fixed-by: is an item of the block, its name not hidden, and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == k()` with the macro-declared `k` (0) and returns 10, and
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

macro_rules! declare_k {
    () => {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    };
}

pub fn host() -> u32 {
    declare_k!();
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        10
    }
    inner()
}
