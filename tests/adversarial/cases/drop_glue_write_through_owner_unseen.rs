//@ expect: reject
//@ mechanism: the value whose drop glue runs a writing `Drop` impl is not the value the host dropped: it
//@ mechanism: is owned by a `Box`, an `Option`, a field of a user struct with no `Drop` impl of its own, a
//@ mechanism: `move` closure, or a `Box<dyn Tr + '_>`. The glue of each owner drops the `G` inside and
//@ mechanism: runs `G::drop`, which sets `c` to 5 through the `&mut` it holds. D-4 gave every `Drop` no
//@ mechanism: logical effect, so each host read `c` after the scope at its value before the borrow.
//@ accept-means: a host is reported `verified` although dropping the owner runs `G::drop`, which sets `c` to
//@ accept-means: 5 before the host returns `c`.
//@ WHY THE CONTRACT IS FALSE: every host returns 5: the owner's glue drops the `G` it holds.
//@ fixed-by: D-140: a `Drop` whose glue may run a writing `Drop` impl, a trait object's or a type
//@ fixed-by: parameter's glue included, re-binds every local the dropped value reaches by reference flow.
//@ teeth: MEASURED: with D-140's hand-off disabled (the parent's behaviour) every host is ACCEPTED,
//@ teeth: exit 0, `verified`; with it each host is `unknown` on the fail-closed return sink.
//@ also-verified: <G<'_> as std::ops::Drop>::drop
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

pub trait Tr {}
impl Tr for G<'_> {}

pub struct W<'a> {
    pub g: G<'a>,
    pub x: u32,
}

#[ensures(result@ == 0)]
pub fn boxed() -> u32 {
    let mut c = 0u32;
    {
        let _b = Box::new(G(&mut c));
    }
    c
}

#[ensures(result@ == 0)]
pub fn optioned() -> u32 {
    let mut c = 0u32;
    {
        let _o = Some(G(&mut c));
    }
    c
}

#[ensures(result@ == 0)]
pub fn field() -> u32 {
    let mut c = 0u32;
    {
        let _w = W { g: G(&mut c), x: 1 };
    }
    c
}

#[ensures(result@ == 0)]
pub fn closure_owned() -> u32 {
    let mut c = 0u32;
    {
        let g = G(&mut c);
        let f = move || {
            let _k = &g;
        };
        let _ = &f;
    }
    c
}

#[ensures(result@ == 0)]
pub fn dyn_boxed() -> u32 {
    let mut c = 0u32;
    {
        let _b: Box<dyn Tr + '_> = Box::new(G(&mut c));
    }
    c
}
