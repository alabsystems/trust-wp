//@ expect: verify
//@ xfail: the price of D-143's premise rule: a proved switch edge is honored only while every premise
//@ xfail: of the proof is an entry fact, and `below`'s postcondition is a premise here. The charge
//@ xfail: `x < 100` is owed after the call and `below` states it, so the edge is truly dead, but the
//@ xfail: premise rule cannot tell a postcondition that holds at the charge from one that does not
//@ xfail: (clause_free_panic_arm_goal_by_later_callee_post.rs), so `f` keeps the cap.
//@ mechanism: control twin of clause_free_panic_arm_goal_by_later_callee_post.rs with the two
//@ mechanism: statements swapped.
//@ teeth: control
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
    assert!(x < 100);
}
