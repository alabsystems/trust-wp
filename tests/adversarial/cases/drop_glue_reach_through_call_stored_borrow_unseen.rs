//@ expect: reject
//@ mechanism: the REACH of drop glue. `v.push(G(&mut c))` stores the guard, and the borrow of `c` in
//@ mechanism: it, into `v` inside the call, and no borrow flows into the call's result. The reference
//@ mechanism: flow of `write_aliases` joins a call's arguments only with a borrow-holding destination, so
//@ mechanism: the component of `v` did not hold `c`, and the `Drop` of `v` at the end of its scope,
//@ mechanism: whose glue runs `G::drop`, re-bound `v` alone. A verified callee that stores the guard
//@ mechanism: into a `&mut` slot it is handed beside it (`store`) is the same shape.
//@ accept-means: a `proof_assert!` is credited although dropping the container ran the guard's `Drop`
//@ accept-means: impl, which set the asserted local to 5.
//@ WHY THE CONTRACT IS FALSE: at each assertion `c` is 5: the container holding the guard was dropped
//@ WHY THE CONTRACT IS FALSE: at the end of its scope and `G::drop` wrote it.
//@ fixed-by: D-140: the glue's reach is taken over a flow graph in which a call also joins its
//@ fixed-by: borrow-holding arguments with one another (`write_aliases::locals_drop_glue_may_change`).
//@ teeth: MEASURED: with D-140's hand-off disabled both assertions are `verified`; with the hand-off
//@ teeth: but the arguments not joined, `vec_push` is still `verified`; with D-140 both are FAILED.
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

pub fn vec_push() {
    let mut c = 0u32;
    {
        let mut v: Vec<G<'_>> = Vec::new();
        v.push(G(&mut c));
    }
    proof_assert!(c@ == 0);
}

#[requires(true)]
pub fn store<'a>(slot: &mut Option<G<'a>>, g: G<'a>) {
    std::mem::forget(std::mem::replace(slot, Some(g)));
}

pub fn user_store() {
    let mut c = 0u32;
    {
        let mut o: Option<G<'_>> = None;
        store(&mut o, G(&mut c));
    }
    proof_assert!(c@ == 0);
}
