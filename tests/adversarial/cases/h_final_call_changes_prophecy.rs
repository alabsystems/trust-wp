//@ expect: reject
//@ mechanism: final-reborrow finality: a store through the parent after the reborrow changes its prophecy (verbatim should_fail/final_borrows::call_changes_prophecy)
//@ accept-means: trust-wp credits a whole-borrow equality (current, final, id) that Creusot's
//@ accept-means: reference semantics cannot prove: the reborrow is NOT final (Creusot emits
//@ accept-means: `borrow_mut`, a fresh unconstrained id and no final link), yet trust-wp links it.
//@ accept-means: Such a credit inside should_fail/final_borrows.rs is a false accept hidden by the
//@ accept-means: test-level rejection.
//@ note: borrow ids are ghost state, so this claim is UNPROVABLE in the reference model rather than
//@ note: concretely refutable (README rule 1): reference/creusot/tests/should_fail/final_borrows/
//@ note: why3session.xml records the id sub-goal failing for every prover.
//@ teeth: pre-fix wp-campaign 6b17a1a — see the per-function verdict recorded in the commit message.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn call_changes_prophecy(bor: &mut i32) {
    #[trusted]
    #[ensures(result@ == 2)]
    fn inner() -> i32 {
        2
    }
    let bor_snap = snapshot!(bor);
    let b1 = &mut *bor;
    let b1_snap = snapshot!(b1);
    *b1 = inner();
    // The prophecy of `bor` changed here after the reborrow
    *bor = inner();
    proof_assert!(*b1_snap == *bor_snap);
}
