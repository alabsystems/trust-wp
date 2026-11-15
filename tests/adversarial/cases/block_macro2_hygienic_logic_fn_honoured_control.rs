//@ expect: verify
//@ mechanism: control: `inner` returns 10, the root's `k()`, which is what the contract's `k` means:
//@ mechanism: the macro's `k` is hidden from it by hygiene. The isolating twin of
//@ mechanism: block_macro2_hygienic_logic_fn_granted.rs (one literal differs).
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
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
        10
    }
    inner()
}
