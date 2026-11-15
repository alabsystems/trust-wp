//@ expect: reject
//@ mechanism: a panic arm's unreachability goal is pushed after BOTH arms of its switch are walked
//@ mechanism: (`handle_bool_switch_with_context`, `handle_int_switch_with_context`), so a callee postcondition
//@ mechanism: assumed in the continuing arm (`below(x)` after the check) is recorded before the goal exists:
//@ mechanism: `scope_call_postconditions_under_preconditions` guards a postcondition only by the obligations
//@ mechanism: recorded before the call. The goal `x < 100` is proved from `below`'s `x@ < 100`, which holds
//@ mechanism: only after the check has passed. `below` diverges for `x >= 100`, so its postcondition is true.
//@ mechanism: the integer-match spelling, clause-free: the `200 =>` arm's goal `!(x == 200)` is proved from
//@ mechanism: the later premise, and a charged edge that leaves the clause-free cap (D-142) credits `f`.
//@ accept-means: a clause-free body that panics for `x == 200` is credited `verified`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200)` panics (a clause-free fn is checked under `requires true`).
//@ teeth: ACCEPTED with this front's charged-edge credit before D-169; at the campaign tip D-142's proved
//@ teeth: edge is withheld by D-143 and `f` is `unknown` (capped). With D-169 the charge is refuted: `f FAILED`.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge, which every sibling arm's edge, a panic arm's included, excludes).
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
