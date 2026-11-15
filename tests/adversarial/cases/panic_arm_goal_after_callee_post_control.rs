//@ expect: verify
//@ xfail: capped by D-143: the charge `x < 100` is proved from `below`'s postcondition, a premise that is no
//@ xfail: entry fact, so D-142's proved edge does not leave the cap: `f unknown (partial: panic paths
//@ xfail: unchecked (panic call))`. Retire this when a decision lifts D-143 for premises D-169 scopes.
//@ mechanism: a panic arm's unreachability goal is pushed after BOTH arms of its switch are walked
//@ mechanism: (`handle_bool_switch_with_context`, `handle_int_switch_with_context`), so a callee postcondition
//@ mechanism: assumed in the continuing arm (`below(x)` after the check) is recorded before the goal exists:
//@ mechanism: `scope_call_postconditions_under_preconditions` guards a postcondition only by the obligations
//@ mechanism: recorded before the call. The goal `x < 100` is proved from `below`'s `x@ < 100`, which holds
//@ mechanism: only after the check has passed. `below` diverges for `x >= 100`, so its postcondition is true.
//@ mechanism: control: the call precedes the panic switch, so its postcondition holds wherever the goal is
//@ mechanism: owed. Twin of assert_arm_goal_discharged_by_later_callee_post.rs with the two statements swapped.
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

pub fn f(x: u32) {
    below(x);
    if x >= 100 {
        panic!()
    }
}
