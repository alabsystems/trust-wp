//@ expect: verify
//@ mechanism: control for logic_fn_body_block_local_name_shadowing_module_name, differing in the claim alone: `result == 10` is what `inner` returns, since its call denotes the block's `k`.
//@ accept-means: n/a (control) — `inner()` is the block's `k()`, which is 10.
//@ mechanism: the body's call is read as rustc resolved it, the block's `k`, since D-174 withholds the root's `k` for a name `host`'s body redeclares; the claim is proved.
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
    fn k() -> Int {
        pearlite! { 10 }
    }

    #[logic]
    #[ensures(result == 10)]
    fn inner() -> Int {
        k()
    }

    0
}
