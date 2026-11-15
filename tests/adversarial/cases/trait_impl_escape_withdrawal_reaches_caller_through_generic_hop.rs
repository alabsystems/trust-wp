//@ expect: reject
//@ mechanism: trait_impl_escape_withdrawal_leaves_trait_callers_credited two calls away: `top`
//@ mechanism: calls the plain generic `mid::<S>`, and `mid` rests on `Tr::m`. The escape join
//@ mechanism: withdraws `<S as Tr>::m`; the trait join's name walk carries a withdrawal along the
//@ mechanism: call graph only from a contract recorded undischarged, so both `mid` and `top` kept
//@ mechanism: their credit while the impl that owed `Tr::m` had lost its own.
//@ accept-means: `mid` and `top` are reported `verified` although `top(Some(0), &[])` panics with
//@ accept-means: "index out of bounds" inside the closure `<S as Tr>::m` hands to `Option::map`.
//@ WHY THE CONTRACT IS FALSE: `top` runs `<S as Tr>::m`, which maps `|j| w[j]` over `Some(0)`
//@ WHY THE CONTRACT IS FALSE: with `w` empty.
//@ fixed-by: D-122: an implementation the escape join withdraws is recorded as not discharging the
//@ fixed-by: contract it owes, and the trait join runs again over every credit still standing.
//@ teeth: MEASURED on the binary before D-122: `<S as Tr>::m` withdrawn, `mid verified ✓` and
//@ teeth: `top verified ✓`. After it `mid` is withdrawn ("it assumed trait method contract
//@ teeth: `Tr::m`") and `top` with it ("through `mid`").
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

#[ensures(result@ == 1)]
pub fn mid<T: Tr>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w)
}

#[ensures(result@ == 1)]
pub fn top(o: Option<usize>, w: &[u32]) -> u32 {
    mid(&S, o, w)
}
