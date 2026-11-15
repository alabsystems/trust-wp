//@ expect: reject
//@ mechanism: trait_impl_escape_withdrawal_leaves_trait_callers_credited one closure deeper: the impl
//@ mechanism: calls a closure it defines, and THAT closure hands `Option::map` a closure indexing an
//@ mechanism: unconstrained slice. The escape join withdraws the impl through the closure it defines;
//@ mechanism: the withdrawal must reach the trait join, which withdraws `generic_caller`.
//@ accept-means: `generic_caller` is reported `verified` although `generic_caller(&S, Some(0), &[])`
//@ accept-means: panics with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `g(Some(0))` maps `|j| w[j]` over `Some(0)` with `w` empty.
//@ fixed-by: D-122: an implementation the escape join withdraws did not discharge the contract it owes.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` withdrawn through the closure it
//@ teeth: defines, `generic_caller verified ✓`. After it `generic_caller` is withdrawn too.
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
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32 {
        let g = |o: Option<usize>| {
            let _ = o.map(|j| w[j]);
        };
        g(o);
        1
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w)
}
