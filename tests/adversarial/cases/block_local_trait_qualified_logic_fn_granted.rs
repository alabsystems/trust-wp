//@ expect: reject
//@ mechanism: `host`'s block declares a trait `Tr` and implements it for the root's `W` with `k` = 0;
//@ mechanism: the crate root declares another `Tr` whose impl for `W` has `k` = 10. Rust resolves the
//@ mechanism: trait in `<W as Tr>::k()`, written in the contract of `inner`, declared in the block, to
//@ mechanism: the block's `Tr`. The resolver looks `Tr` up among the children of the owner's MODULE,
//@ mechanism: takes the root's trait, and `inner`, which returns 10, is verified against a contract it
//@ mechanism: violates.
//@ fixed-by: D-195 — a contract name is resolved through the block scopes around the clause before the
//@ fixed-by: owner's module (`logic::block_scope::lookup`), as rustc resolves it: `Tr` is the block's
//@ fixed-by: trait, whose impl for `W` has `k` = 0, and the function returning 10 is refuted.
//@ accept-means: `inner` claims `result@ == <W as Tr>::k()` with the block's `Tr` (0) and returns 10,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`host::inner verified ✓`). With D-195: `host::inner FAILED ✗
//@ teeth: (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W;
pub trait Tr {
    #[logic]
    fn k() -> Int;
}
impl Tr for W {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 10 }
    }
}

pub fn host() -> u32 {
    trait Tr {
        #[logic]
        fn k() -> Int;
    }
    impl Tr for W {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    #[ensures(result@ == <W as Tr>::k())]
    fn inner() -> u32 {
        10
    }
    inner()
}
