//@ expect: reject
//@ mechanism: a logic function `j` declared in `host`'s block has the body `k()`, and the block
//@ mechanism: declares a logic function `k` (0); the crate root declares another `k` (10). Rust
//@ mechanism: resolves the `k` in `j`'s body in the block, so `j` is 0. A logic function's body is
//@ mechanism: resolved in its own scope as an axiom (`ResolveMode::LogicDef`) apart from the contracts
//@ mechanism: that call it: if that pass read `k` in the module while the contract's `j` is read in the
//@ mechanism: block, `j` would be defined as the root's 10 and `inner`, which returns 10, would be
//@ mechanism: verified against `result@ == j()` = 0.
//@ fixed-by: not a defect at the head that committed it (the contract's `j`, declared only in the
//@ fixed-by: block, was refused): the guard case that the definition pass reads block scopes as the
//@ fixed-by: contract pass does.
//@ accept-means: `inner` claims `result@ == j()` with `j` = the block's `k` = 0, returns 10, and the
//@ accept-means: crate exits 0.
//@ teeth: MEASURED with the block lookup disabled for logic-function definitions only by a local knob:
//@ teeth: ACCEPTED at exit 0 (`host::inner verified ✓`); with it, `host::inner FAILED ✗
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

pub fn host() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 0 }
    }
    #[logic(open)]
    fn j() -> Int {
        pearlite! { k() }
    }
    #[ensures(result@ == j())]
    fn inner() -> u32 {
        10
    }
    inner()
}
