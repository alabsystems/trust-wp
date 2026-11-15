//@ expect: reject
//@ mechanism: a function whose loops carry an invariant takes its premises from
//@ mechanism: `collect_call_effects_for_blocks`, a flat walk over the non-loop blocks that keeps no path:
//@ mechanism: a callee postcondition recorded for one block is a premise of every goal of the function VC,
//@ mechanism: guarded only by the obligations of the blocks that can reach its call
//@ mechanism: (`guard_assumptions_by_reaching_obligations`).
//@ mechanism: the clause-free post-loop spelling of loop_invariant_fn_post_loop_callee_post_on_other_arm.rs:
//@ mechanism: the call and the panic switch follow the loop, and `f` carries no clause.
//@ accept-means: a contract-free body that panics on the path that skips the call is credited as panic-free.
//@ WHY THE CONTRACT IS FALSE: `f(200, false)` panics (a contract-free fn is checked under `requires true`).
//@ teeth: ACCEPTED before D-169 and with it; not an effect of D-142, whose edges are
//@ teeth: recorded only by the loop-free walk.
//@ also-verified: below
//@ fixed-by: D-243: each premise of the block-slice walker is stated under a formula that holds only where its block
//@ fixed-by: runs, and each goal under one that holds wherever it runs (`call_effect_reach::BlockReach`).
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

pub fn f(x: u32, flag: bool) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    if flag {
        below(x);
    }
    if x >= 100 {
        panic!()
    }
}
