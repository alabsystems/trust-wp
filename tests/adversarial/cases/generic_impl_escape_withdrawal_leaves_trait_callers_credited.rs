//@ expect: reject
//@ mechanism: trait_impl_escape_withdrawal_leaves_trait_callers_credited on a GENERIC impl:
//@ mechanism: `impl<T: Tr> Tr2 for W<T>` hands `Option::map` a closure that calls `Tr::m` on its
//@ mechanism: field, and `<S as Tr>::m` hands `Option::map` a closure that indexes an
//@ mechanism: unconstrained slice. The escape join withdraws both impls; `<W<T> as Tr2>::n` owes
//@ mechanism: `Tr2::n` for every `T`, so its withdrawal must reach the trait join, which withdraws
//@ mechanism: `caller2`, resting on `Tr2::n`, and `top`, which calls `caller2::<W<S>>`.
//@ accept-means: `caller2` and `top` are reported `verified` although `top(Some(0), &[])` panics
//@ accept-means: with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `top` runs `<W<S> as Tr2>::n`, whose closure calls `<S as Tr>::m(0, &[])`,
//@ WHY THE CONTRACT IS FALSE: which maps `|j| w[j]` over `Some(0)` with `w` empty.
//@ fixed-by: D-122: an implementation the escape join withdraws did not discharge the contract it
//@ fixed-by: owes, and the trait join runs again over every credit still standing.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` and `<W<T> as Tr2>::n` withdrawn,
//@ teeth: `caller2 verified ✓` and `top verified ✓`. After it `caller2` is withdrawn ("it assumed
//@ teeth: trait method contract `Tr2::n`") and `top` with it ("through `caller2`").
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
    #[requires(x@ < 2)]
    #[ensures(result@ == 1)]
    fn m(&self, x: usize, w: &[u32]) -> u32;
}

pub struct S;

impl Tr for S {
    #[requires(x@ < 2)]
    #[ensures(result@ == 1)]
    fn m(&self, x: usize, w: &[u32]) -> u32 {
        let _ = Some(x).map(|j| w[j]);
        1
    }
}

pub trait Tr2 {
    #[ensures(result@ == 1)]
    fn n(&self, o: Option<usize>, w: &[u32]) -> u32;
}

pub struct W<T>(pub T);

impl<T: Tr> Tr2 for W<T> {
    #[ensures(result@ == 1)]
    fn n(&self, o: Option<usize>, w: &[u32]) -> u32 {
        let inner = &self.0;
        let _ = o.map(|j| inner.m(j % 2, w));
        1
    }
}

#[ensures(result@ == 1)]
pub fn caller2<T: Tr2>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.n(o, w)
}

#[ensures(result@ == 1)]
pub fn top(o: Option<usize>, w: &[u32]) -> u32 {
    caller2(&W(S), o, w)
}
