//@ expect: reject
//@ mechanism: a function whose loops carry an invariant takes its premises from
//@ mechanism: `collect_call_effects_for_blocks`, a flat walk over the non-loop blocks that keeps no path:
//@ mechanism: a callee postcondition recorded for one block is a premise of every goal of the function VC,
//@ mechanism: guarded only by the obligations of the blocks that can reach its call
//@ mechanism: (`guard_assumptions_by_reaching_obligations`). D-169 scopes the primary walk's premises to
//@ mechanism: their arm; this lane is not the primary walk, and its premises are scoped to nothing.
//@ mechanism: the invariant spelling: the premise of the `flag` arm proves the invariant on loop entry on the
//@ mechanism: path that skips the call.
//@ accept-means: an invariant false on entry on one path is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false)` enters the loop with `x == 200`, so `x@ < 100` does not hold.
//@ teeth: ACCEPTED at the campaign tip and with D-169.
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

#[ensures(true)]
pub fn f(x: u32, flag: bool) {
    if flag {
        below(x);
    }
    let mut i = 0u32;
    #[invariant(x@ < 100)]
    while i < 3 {
        i += 1;
    }
}
