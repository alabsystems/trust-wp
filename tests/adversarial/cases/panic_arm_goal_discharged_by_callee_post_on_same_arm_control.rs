//@ expect: verify
//@ xfail: capped by D-143: the charge is proved from `below`'s postcondition, scoped to the `flag` arm by
//@ xfail: D-169, a premise that is no entry fact, so D-142's proved edge does not leave the cap:
//@ xfail: `f unknown (partial: panic paths unchecked (panic call))`. Retire this when a decision lifts D-143
//@ xfail: for premises D-169 scopes.
//@ mechanism: the primary walk keeps call effects in flat lists, and every goal is proved under every
//@ mechanism: assumption. A callee postcondition assumed while walking ONE arm of a switch (`below(x)` on
//@ mechanism: the `flag` arm, `ensures(x@ < 100)`) is therefore a premise of the goals the walk states on
//@ mechanism: the other path too: `scope_call_postconditions_under_preconditions` guards it by the
//@ mechanism: obligations recorded so far, never by the guard of the arm it was assumed on. `below`
//@ mechanism: diverges for `x >= 100`, so its postcondition is true, but it says nothing about an
//@ mechanism: execution that never calls it.
//@ mechanism: control: the call and the panic switch are on the same arm, so the postcondition holds
//@ mechanism: wherever the panic goal is owed. Twin of panic_arm_goal_discharged_by_callee_post_on_other_arm.rs.
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

pub fn f(x: u32, flag: bool) {
    if flag {
        below(x);
        if x >= 100 {
            panic!()
        }
    }
}
