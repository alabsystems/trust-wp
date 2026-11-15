//@ expect: reject
//@ mechanism: the call-result edge (`PremiseEdge`) when the result is bound to a user variable and the
//@ mechanism: call's argument is written before the switch: `c` is still defined only by the call, never
//@ mechanism: borrowed, so `$call` names the value `if c` tests, and `below`'s premise is scoped to it. The
//@ mechanism: panic goal after the join is owed on both paths.
//@ accept-means: a body that panics on the path that skips the call is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, &mut 500)` skips `below` and panics.
//@ teeth: ACCEPTED at the campaign tip, where the arm's premise is unscoped; rejected with D-169.
//@ also-verified: pick, below, small
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@ % 3)]
pub fn pick(x: &u32) -> u32 {
    *x % 3
}

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(result == (x@ < 100))]
pub fn small(x: &u32) -> bool {
    *x < 100
}

#[ensures(true)]
pub fn f(x: u32, a: &mut u32) {
    let c = small(a);
    *a = 7;
    if c {
        below(x);
    }
    if x >= 100 {
        panic!()
    }
}
