//@ expect: reject
//@ mechanism: a `macro` 2.0 invoked in `host`'s block declares a logic function `k` (0); the crate root
//@ mechanism: declares another `k` (10). A `macro` 2.0 item is hygienic: its name carries the macro's
//@ mechanism: opaque mark, so the `k` written in the contract of `inner`, at the root context, cannot
//@ mechanism: see it, and Rust resolves it to the root's `k`. `inner` returns 0 against `result@ ==
//@ mechanism: 10`. A block lookup that matched names by spelling alone would read the macro's `k` and
//@ mechanism: credit `inner`; the lookup skips an item whose name keeps an opaque mark, and refuses
//@ mechanism: every name of an owner that carries one.
//@ fixed-by: not a defect at the head that committed it: the guard case of the block-scope lookup's
//@ fixed-by: hygiene check.
//@ accept-means: `inner` claims `result@ == k()` with the root's `k` (10) and returns 0, and the crate
//@ accept-means: exits 0.
//@ teeth: MEASURED with the hygiene check disabled by a local knob (the name compared by spelling
//@ teeth: only): ACCEPTED at exit 0 (`host::inner verified ✓`); with it, `host::inner FAILED ✗
//@ teeth: (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(decl_macro)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub fn host() -> u32 {
    macro declare_k() {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    declare_k!();
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        0
    }
    inner()
}
