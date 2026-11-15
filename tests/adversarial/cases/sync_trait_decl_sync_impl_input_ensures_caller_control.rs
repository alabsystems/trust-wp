//@ expect: verify
//@ mechanism: over-refusal control and isolating twin of sync_trait_decl_async_impl_input_ensures_granted_to_caller:
//@ mechanism: the same sync declaration over a by-value input and the same generic callers, with a sync
//@ mechanism: impl that the contract loop verifies against the declaration. The grant is discharged, so
//@ mechanism: the callers' credits stand; only a refused implementation withdraws them. The declaration
//@ mechanism: and the callers carry `requires(x@ >= 5)` because no implementation meets `x@ >= 5` for
//@ mechanism: every input.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control): the impl meets the declaration, so each caller's claim holds.
//@ teeth: n/a: over-refusal control; `<S as Tr>::m`, `f` and `g` verified at D-140's head.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::future::Future;

pub trait Tr {
    #[requires(x@ >= 5)]
    #[ensures(x@ >= 5)]
    fn m(&self, x: u32) -> impl Future<Output = ()>;
}

pub struct S;
impl Tr for S {
    #[requires(x@ >= 5)]
    #[ensures(x@ >= 5)]
    fn m(&self, x: u32) -> impl Future<Output = ()> {
        let _ = x;
        async {}
    }
}

#[requires(a@ >= 5)]
#[ensures(result@ >= 5)]
pub fn f<T: Tr>(t: &T, a: u32) -> u32 {
    drop(t.m(a));
    a
}

#[requires(a@ >= 5)]
#[ensures(result@ >= 5)]
pub fn g<T: Tr>(t: &T, a: u32) -> u32 {
    let _fut = t.m(a);
    a
}
