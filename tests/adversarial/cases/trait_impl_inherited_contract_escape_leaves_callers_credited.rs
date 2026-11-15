//@ expect: reject
//@ mechanism: trait_impl_escape_withdrawal_leaves_trait_callers_credited with an impl that writes no
//@ mechanism: clause of its own: `<S as Tr>::m` inherits `Tr::m`'s `ensures`, is verified against it,
//@ mechanism: and is withdrawn by the escape join for the closure it hands `Option::map`. The
//@ mechanism: withdrawal must reach the trait join as for an impl that restates the contract.
//@ accept-means: `generic_caller` is reported `verified` although `generic_caller(&S, Some(0), &[])`
//@ accept-means: panics with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `generic_caller::<S>` runs `<S as Tr>::m`, which maps `|j| w[j]`
//@ WHY THE CONTRACT IS FALSE: over `Some(0)` with `w` empty.
//@ fixed-by: D-122: an implementation the escape join withdraws did not discharge the contract it
//@ fixed-by: owes, inherited or restated.
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
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32;
}

pub struct S;

impl Tr for S {
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32 {
        let _ = o.map(|j| w[j]);
        1
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w)
}
