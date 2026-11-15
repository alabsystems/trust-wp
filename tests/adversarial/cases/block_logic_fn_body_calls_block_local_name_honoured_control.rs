//@ expect: verify
//@ mechanism: control: `inner` returns 0, which is `j()`, the block's `k()`. The isolating twin of
//@ mechanism: block_logic_fn_body_calls_block_local_name_granted.rs (one literal differs).
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; refused before the block lookup, `j` resolving nowhere)
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
        0
    }
    inner()
}
