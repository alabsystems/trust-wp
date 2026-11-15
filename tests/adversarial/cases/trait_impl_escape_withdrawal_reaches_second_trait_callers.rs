//@ expect: reject
//@ mechanism: the escape join withdraws `<S as Tr>::m`; `<U as Tr2>::n` calls it pinned, and
//@ mechanism: `caller2` rests on `Tr2::n`. Only a trait join that sees the escape withdrawal carries
//@ mechanism: it on: `<U as Tr2>::n` rests on `Tr::m` where `<S as Tr>::m` runs, and
//@ mechanism: `caller2` rests on `Tr2::n`, which that impl left undischarged.
//@ accept-means: `<U as Tr2>::n` and `caller2` are reported `verified` although
//@ accept-means: `caller2(&U, Some(0), &[])` panics with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `caller2::<U>` runs `<S as Tr>::m`, which maps `|j| w[j]` over
//@ WHY THE CONTRACT IS FALSE: `Some(0)` with `w` empty.
//@ fixed-by: D-122: the escape and trait joins feed one ledger, run to a fixpoint.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` withdrawn, `<U as Tr2>::n verified ✓`
//@ teeth: and `caller2 verified ✓`. After it both are withdrawn: `<U as Tr2>::n` rests on
//@ teeth: `<S as Tr>::m`, and `caller2` on `Tr2::n`, which that impl left undischarged.
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
        let _ = o.map(|j| w[j]);
        1
    }
}

pub trait Tr2 {
    #[ensures(result@ == 1)]
    fn n(&self, o: Option<usize>, w: &[u32]) -> u32;
}

pub struct U;

impl Tr2 for U {
    #[ensures(result@ == 1)]
    fn n(&self, o: Option<usize>, w: &[u32]) -> u32 {
        S.m(o, w)
    }
}

#[ensures(result@ == 1)]
pub fn caller2<T: Tr2>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.n(o, w)
}
