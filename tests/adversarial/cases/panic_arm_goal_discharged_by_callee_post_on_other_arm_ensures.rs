//@ expect: reject
//@ mechanism: the primary walk keeps call effects in flat lists, and every goal is proved under every
//@ mechanism: assumption. A callee postcondition assumed while walking ONE arm of a switch (`below(x)` on
//@ mechanism: the `flag` arm, `ensures(x@ < 100)`) is therefore a premise of the goals the walk states on
//@ mechanism: the other path too: `scope_call_postconditions_under_preconditions` guards it by the
//@ mechanism: obligations recorded so far, never by the guard of the arm it was assumed on. `below`
//@ mechanism: diverges for `x >= 100`, so its postcondition is true, but it says nothing about an
//@ mechanism: execution that never calls it.
//@ mechanism: here `f` carries a clause, so no cap applies: the panic goal `!flag ==> !(x >= 100)` is
//@ mechanism: proved from the premise and `f` is verified.
//@ accept-means: a body that panics on the path that skips the call is verified against its contract,
//@ accept-means: and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false)` panics, and a function with a contract must not panic.
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
pub fn f(x: u32, flag: bool) {
    if flag {
        below(x);
    }
    if x >= 100 {
        panic!()
    }
}
