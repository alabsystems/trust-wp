//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: host::<impl S>::g
//@ mechanism: an inherent impl of a module-level type `S` declared in a function's BLOCK is visible to the
//@ mechanism: whole crate, so `caller` at module scope calls `S::g`, whose `ensures` names `k`. Rust reads
//@ mechanism: that `k` in `g`'s own scope, the block's `k` (0), not the crate root's (10). The grant (`g`'s
//@ mechanism: verification) and the obligation (`caller`'s use of `g`'s contract, `resolve_spec_clauses_in_scope`
//@ mechanism: with the callee's `DefId`) must both read the block's `k` (D-195): `g`, which returns 0,
//@ mechanism: verifies, and `caller`, claiming 10, is refuted. Its one-literal TRUE twin is
//@ mechanism: block_local_impl_method_contract_read_at_module_caller_control.rs.
//@ fixed-by: D-195 — the block scopes around a clause are read before the owner's module, for the callee's
//@ fixed-by: own verification and for its contract read at a call site alike.
//@ accept-means: `caller` is credited with `result@ == 10` for `s.g()`, which returns 0.
//@ teeth: MEASURED, isolating pair: with the module lookup alone (the campaign tip this branch was built on)
//@ teeth: `host::<impl S>::g` is FAILED and `caller` verified, then withdrawn as resting on a failed
//@ teeth: contract, and the twin has both FAILED; with D-195 `g` verifies and `caller` is FAILED here, and
//@ teeth: both verify in the twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub struct S;

pub fn host() {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 0 }
    }
    impl S {
        #[ensures(result@ == k())]
        pub fn g(&self) -> u32 {
            0
        }
    }
}

// WRONG: `S::g` returns 0; its contract reads the block's `k`.
#[ensures(result@ == 10)]
pub fn caller(s: &S) -> u32 {
    s.g()
}
