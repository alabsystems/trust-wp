//@ expect: verify
//@ mechanism: a function whose loops carry an invariant takes its premises from
//@ mechanism: `collect_call_effects_for_blocks`, a flat walk over the non-loop blocks that keeps no path:
//@ mechanism: a callee postcondition recorded for one block is a premise of every goal of the function VC,
//@ mechanism: guarded only by the obligations of the blocks that can reach its call
//@ mechanism: (`guard_assumptions_by_reaching_obligations`). D-169 scopes the primary walk's premises to
//@ mechanism: their arm; this lane is not the primary walk, and its premises are scoped to nothing.
//@ mechanism: control: the call and the panic switch are on the same arm, so the postcondition holds wherever
//@ mechanism: the panic goal is owed. Twin of loop_invariant_fn_callee_post_on_other_arm_discharges_panic_goal.rs.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
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
        if x >= 100 {
            panic!()
        }
    }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
