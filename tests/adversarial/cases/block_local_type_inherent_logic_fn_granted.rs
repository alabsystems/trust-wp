//@ expect: reject
//@ mechanism: `host`'s block declares a struct `W` with an inherent logic function `k` (0); the crate
//@ mechanism: root declares another `W` whose `k` is 10. Rust resolves the first segment of `W::k()` in
//@ mechanism: the contract of `inner`, declared in the block, to the block's `W`. The resolver looks
//@ mechanism: `W` up among the children of the owner's MODULE (`Resolver::resolve_prefix`), takes the
//@ mechanism: root's `W`, and `inner`, which returns 10, is verified against a contract it violates.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: the first segment `W`
//@ fixed-by: is the block's struct, whose `k` is 0, and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == W::k()` with the block's `W` (0) and returns 10, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`). With D-195: `host::inner FAILED ✗
//@ teeth: (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W;
impl W {
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 10 }
    }
}

pub fn host() -> u32 {
    struct W;
    impl W {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    #[ensures(result@ == W::k())]
    fn inner() -> u32 {
        10
    }
    inner()
}
