//@ expect: reject
//@ mechanism: the primary walk keeps call effects in flat lists, and every goal is proved under every
//@ mechanism: assumption. A callee postcondition assumed while walking ONE arm of a switch (`below(x)` on
//@ mechanism: the `flag` arm, `ensures(x@ < 100)`) is therefore a premise of the goals the walk states on
//@ mechanism: the other path too: `scope_call_postconditions_under_preconditions` guards it by the
//@ mechanism: obligations recorded so far, never by the guard of the arm it was assumed on. `below`
//@ mechanism: diverges for `x >= 100`, so its postcondition is true, but it says nothing about an
//@ mechanism: execution that never calls it.
//@ mechanism: the overflow spelling: the charged `x + 1` goal on the `!flag` path is proved from the
//@ mechanism: premise, and the arithmetic lane credits it with no cap involved.
//@ accept-means: a clause-free body whose `x + 1` overflows on the path that skips the call is credited
//@ accept-means: `verified`.
//@ WHY THE CONTRACT IS FALSE: `f(u32::MAX, false)` overflows (a clause-free fn is checked under `requires true`).
//@ teeth: ACCEPTED at the campaign tip, and with wp-s120's panic-arm edge credit: the premise is unscoped in the WP core.
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

pub fn f(x: u32, flag: bool) -> u32 {
    if flag {
        below(x);
    }
    x + 1
}
