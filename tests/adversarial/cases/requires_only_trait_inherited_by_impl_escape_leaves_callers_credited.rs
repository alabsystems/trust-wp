//@ expect: reject
//@ mechanism: trait_impl_escape_withdrawal_leaves_trait_callers_credited for a trait method whose
//@ mechanism: contract is a `requires` alone, INHERITED by an impl that writes no clause. The trait
//@ mechanism: join settles such an impl by what its own verification reported, and a requires-only
//@ mechanism: contract hands a caller no postcondition, so silence is no shortfall there. The impl
//@ mechanism: is credited, then the escape join withdraws it for the closure it hands to
//@ mechanism: `Option::map`; that withdrawal must reach the trait join as for an impl that restates
//@ mechanism: the contract.
//@ accept-means: `generic_caller` is reported `verified` although `generic_caller(&S, Some(0), &[])`
//@ accept-means: panics with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `generic_caller::<S>` runs `<S as Tr>::m`, which maps `|j| w[j]` over
//@ WHY THE CONTRACT IS FALSE: `Some(0)` with `w` empty.
//@ fixed-by: D-122: an implementation the escape join withdraws did not discharge the contract it
//@ fixed-by: owes, inherited or restated, with postconditions or without.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` withdrawn for the closure it hands
//@ teeth: over, `generic_caller verified ✓`. After it `generic_caller` is withdrawn ("it assumed
//@ teeth: trait method contract `Tr::m`").
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
    fn m(&self, o: Option<usize>, w: &[u32]) {
        let _ = o.map(|j| w[j]);
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w);
    1
}
