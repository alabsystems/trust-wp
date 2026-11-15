//@ expect: reject
//@ mechanism: the refused-implementation ledger reached with no drop-glue hand-off on the way. The trait
//@ mechanism: DECLARATION is a sync method returning `impl Future`; its `ensures` speaks of a by-value
//@ mechanism: input, so a generic caller that builds the future and drops it (`mem::drop`, or at its
//@ mechanism: scope end) keeps the premise `a@ >= 5` for a value no borrow reaches. The only
//@ mechanism: implementation is an `async fn`, which the contract loop refuses, so the caller's grant rests
//@ mechanism: on a contract nothing discharged. sync_trait_decl_async_impl_ensures_granted_to_caller is the
//@ mechanism: `&mut` spelling, which D-140's hand-off now rejects before the ledger is read.
//@ accept-means: a caller keeps a trait-contract credit whose only implementation was refused.
//@ WHY IT IS FALSE: `f(&S, 0)` and `g(&S, 0)` return 0 and claim `result@ >= 5`.
//@ teeth: MEASURED at D-140's head: `f verified ✓` and `g verified ✓` from the contract loop, then each
//@ teeth: `error: verdict withdrawn - it assumed trait method contract `Tr::m` (`<S as Tr>::m` was refused,
//@ teeth: not verified)`. So each credit rests on the declaration's grant alone and only the ledger takes
//@ teeth: it back. The isolating twin is sync_trait_decl_sync_impl_input_ensures_caller_control: a sync
//@ teeth: impl that the loop verifies, where the caller's credit stands.
//@ fixed-by: D-117: `TraitCreditJoin::refused` records a refused implementation of a contracted trait
//@ fixed-by: method as undischarged.
//@ verdict: unknown
//@ refused-with: verdict withdrawn - it assumed trait method contract `Tr::m` (`<S as Tr>::m` was refused
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::future::Future;

pub trait Tr {
    #[ensures(x@ >= 5)]
    fn m(&self, x: u32) -> impl Future<Output = ()>;
}

pub struct S;
impl Tr for S {
    async fn m(&self, _x: u32) {}
}

#[ensures(result@ >= 5)]
pub fn f<T: Tr>(t: &T, a: u32) -> u32 {
    drop(t.m(a));
    a
}

#[ensures(result@ >= 5)]
pub fn g<T: Tr>(t: &T, a: u32) -> u32 {
    let _fut = t.m(a);
    a
}
