//@ expect: reject
//@ mechanism: the trait DECLARATION is a sync method returning `impl Future`, so its `ensures` is a claim about the call and is rightly granted at a generic call site; the impl meets the signature with an `async fn`, which the contract loop refuses. The trait-credit ledger withdraws a caller's credit only when an implementation records a shortfall, and a refusal recorded none: the loop reached the impl and never closed it. The caller kept a credit resting on an implementation that discharged nothing.
//@ accept-means: a caller keeps a trait-contract credit whose only implementation was refused.
//@ WHY IT IS FALSE: the future is dropped unpolled, so `f` returns 0 and claims `result@ == 5`. The impl, whose body runs only when the future is polled, does not meet the declaration's claim about the call.
//@ teeth: MEASURED on the parent: `<S as Tr>::m` refused, `f verified ✓`. At the fix: `f error: verdict withdrawn`, naming `<S as Tr>::m` as refused. The isolating twin is sync_trait_decl_sync_impl_ensures_caller_control: the same declaration and caller, and a sync impl that writes 5 before returning a ready future; there `f` verifies.
//@ teeth: Since D-140 the drop of the generic future is itself a hand-off: another implementation's future may write `y` when it is dropped, so `y` is re-bound there and `f` is `unknown` before the ledger is read. MEASURED on D-140's head with its hand-off disabled: `f verified ✓`, then `f error: verdict withdrawn`; with it, `f unknown` (refutation withheld). Forgetting the future instead is no way round: with `mem::forget` in place of `drop`, `f` is `unknown` on a fail-closed `false` with the hand-off disabled as well. So while D-140 stands this case is rejected by the hand-off and no longer reaches the refused-implementation ledger; it no longer names the ledger's line. sync_trait_decl_async_impl_input_ensures_granted_to_caller reaches the ledger over a by-value input no hand-off re-binds, and names it.
//@ fixed-by: D-117 — `TraitCreditJoin::refused` records a refused implementation of a contracted trait method as undischarged
//@ verdict: unknown
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
    async fn m(&self, x: &mut u32) {
        *x = 5;
    }
}

#[ensures(result@ == 5)]
pub fn f<T: Tr>(t: &T) -> u32 {
    let mut y = 0u32;
    drop(t.m(&mut y));
    y
}
