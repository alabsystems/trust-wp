//@ expect: reject
//@ mechanism: the UNSEEN-WRITE spelling of trait_impl_escape_withdrawal_leaves_trait_callers_credited:
//@ mechanism: `<S as Tr>::m` hands `Option::map` a closure that writes its captured `c`, which the
//@ mechanism: impl's proof reads at its value before the call; the escape join withdraws the impl, and
//@ mechanism: the withdrawal must reach the trait join, which withdraws `generic_caller`.
//@ accept-means: `generic_caller` is reported `verified` although `generic_caller(&S, Some(0))`
//@ accept-means: returns 5.
//@ WHY THE CONTRACT IS FALSE: with `o = Some(_)` the closure runs and sets `c = 5` before `m`
//@ WHY THE CONTRACT IS FALSE: returns `c`.
//@ fixed-by: D-122: an implementation the escape join withdraws did not discharge the contract it owes.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` withdrawn for the unseen write,
//@ teeth: `generic_caller verified ✓`. After it `generic_caller` is withdrawn too.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

pub trait Tr {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>) -> u32 {
        let mut c = 1u32;
        let _ = o.map(|_| c = 5);
        c
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>) -> u32 {
    t.m(o)
}
