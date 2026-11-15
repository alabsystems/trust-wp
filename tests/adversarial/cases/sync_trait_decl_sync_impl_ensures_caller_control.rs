//@ expect: verify
//@ mechanism: over-refusal control and isolating twin of sync_trait_decl_async_impl_ensures_granted_to_caller: the same declaration and the same generic caller, with a sync impl that writes 5 before it returns a ready future. That impl is verified against the declaration's `ensures`, so the caller's grant is discharged and stands; only a refused implementation withdraws it.
//@ fixed-by: n/a (control)
//@ xfail: D-107's price. The declaration returns `impl Future`, which captures `x`'s borrow, so `(^x)@ == 5` is refused at parse ("another parameter or the returned value may hold its borrow after the call"): the future could write `x` after `m` returns, and no prophecy records that write. The impl is then unproved and `f`'s grant is withdrawn.
//@ accept-means: n/a (control) — the impl meets the declaration at the call, so `f`'s claim holds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::future::Future;

pub trait Tr {
    #[ensures((^x)@ == 5)]
    fn m(&self, x: &mut u32) -> impl Future<Output = ()>;
}

pub struct S;
impl Tr for S {
    fn m(&self, x: &mut u32) -> impl Future<Output = ()> {
        *x = 5;
        async {}
    }
}

#[ensures(result@ == 5)]
pub fn f<T: Tr>(t: &T) -> u32 {
    let mut y = 0u32;
    drop(t.m(&mut y));
    y
}
