//@ expect: reject
//@ mechanism: trait_impl_escape_withdrawal_leaves_trait_callers_credited for a trait method whose
//@ mechanism: contract is a `requires` alone: the caller is handed no postcondition, only the
//@ mechanism: absence of a panic under that precondition, and the impl the escape join withdraws
//@ mechanism: panics inside the closure it hands to `Option::map`.
//@ accept-means: `generic_caller` is reported `verified` although `generic_caller(&S, Some(0), &[])`
//@ accept-means: panics with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `generic_caller::<S>` runs `<S as Tr>::m`, which maps `|j| w[j]` over
//@ WHY THE CONTRACT IS FALSE: `Some(0)` with `w` empty.
//@ fixed-by: D-122: an implementation the escape join withdraws did not discharge the contract it owes.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` withdrawn, `generic_caller verified ✓`.
//@ teeth: After it `generic_caller` is withdrawn ("it assumed trait method contract `Tr::m`").
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
    #[requires(true)]
    fn m(&self, o: Option<usize>, w: &[u32]);
}

pub struct S;

impl Tr for S {
    #[requires(true)]
    fn m(&self, o: Option<usize>, w: &[u32]) {
        let _ = o.map(|j| w[j]);
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w);
    1
}
