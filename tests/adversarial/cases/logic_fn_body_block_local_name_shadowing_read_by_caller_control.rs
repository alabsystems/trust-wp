//@ expect: verify
//@ mechanism: control for logic_fn_body_block_local_name_shadowing_read_by_caller, differing in the block's own `k` alone: without it `inner`'s `k()` is the root's, 0, the identity pass and rustc name the same definition, and `outer` unfolds `inner` to prove `result == 0`.
//@ accept-means: n/a (control) — `outer()` is `inner()`, which is the root's `k()`, 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 0 }
}

pub fn host() -> u32 {
    #[logic(open)]
    fn inner() -> Int {
        k()
    }

    #[logic]
    #[ensures(result == 0)]
    fn outer() -> Int {
        inner()
    }

    0
}
