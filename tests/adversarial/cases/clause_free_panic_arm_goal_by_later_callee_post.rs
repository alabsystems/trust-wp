//@ expect: reject
//@ mechanism: D-142 reads a switch edge as dead when the walk's charge that the arm is not taken is
//@ mechanism: proved. The charge is a goal proved from the verdict's premises, and the primary walk
//@ mechanism: records a callee postcondition as a premise of every goal: it is guarded by the
//@ mechanism: obligations recorded before the call, never by the switch arm the call sits in, and the
//@ mechanism: `assert!` arm's charge is pushed after the continuing arm (`below(x)`) was walked. So the
//@ mechanism: charge `x < 100` is proved from `below`'s `x@ < 100`, a fact only of the path that passed
//@ mechanism: the check. `below` diverges for `x >= 100`, so its postcondition is true.
//@ accept-means: a clause-free body whose `assert!` fails is credited `verified`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200)` panics at the `assert!` (a clause-free fn is checked under
//@ WHY THE CONTRACT IS FALSE: `requires true`).
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below
//@ teeth: MEASURED ACCEPTED under D-142 before D-143: `f verified`, exit 0. Rejected
//@ teeth: once `partial_verdict::dead_edges_the_proof_owns` honors an edge only while every premise is
//@ teeth: an entry fact: `f` keeps the cap, `unknown (partial: panic paths unchecked (panic call))`.
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
    assert!(x < 100);
    below(x);
}
