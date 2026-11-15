//@ expect: reject
//@ mechanism: the int-switch twin of clause_free_panic_arm_goal_by_later_callee_post.rs: the `200` arm's
//@ mechanism: charge `!(x == 200)` is pushed after the otherwise arm, which calls `below(x)`, was walked,
//@ mechanism: and `below`'s `x@ < 100` premises it. D-142 read the charged edge as dead.
//@ accept-means: a clause-free body that panics for `x == 200` is credited `verified`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200)` panics (a clause-free fn is checked under `requires true`).
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below
//@ teeth: MEASURED ACCEPTED under D-142 before D-143: `f verified`, exit 0.
//@ teeth: With D-169 the charge itself is refuted, so `f FAILED` before any cap is read.
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
    match x {
        200 => panic!(),
        _ => {}
    }
    below(x);
}
