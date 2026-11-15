//@ expect: reject
//@ mechanism: a panic arm's unreachability goal is pushed after BOTH arms of its switch are walked
//@ mechanism: (`handle_bool_switch_with_context`, `handle_int_switch_with_context`), so a callee postcondition
//@ mechanism: assumed in the continuing arm (`below(x)` after the check) is recorded before the goal exists:
//@ mechanism: `scope_call_postconditions_under_preconditions` guards a postcondition only by the obligations
//@ mechanism: recorded before the call. The goal `x < 100` is proved from `below`'s `x@ < 100`, which holds
//@ mechanism: only after the check has passed. `below` diverges for `x >= 100`, so its postcondition is true.
//@ mechanism: here `f` carries a clause, so no cap applies: the `assert!` goal is proved from the later
//@ mechanism: premise and `f` is verified.
//@ accept-means: a body whose `assert!` fails is verified against its contract, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200)` panics at the `assert!`, and a function with a contract must not panic.
//@ teeth: ACCEPTED at the campaign tip, and with wp-s120's panic-arm edge credit: the premise is unscoped in the WP core, not in the cap.
//@ teeth: Rejected with D-169.
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

#[ensures(true)]
pub fn f(x: u32) {
    assert!(x < 100);
    below(x);
}
