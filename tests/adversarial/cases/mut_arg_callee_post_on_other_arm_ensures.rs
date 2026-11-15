//@ expect: reject
//@ mechanism: the `&mut`-argument spelling of an arm premise (D-169): `set_below(&mut y, x)` on the `flag`
//@ mechanism: arm assumes its postcondition `x@ < 100 && (^r)@ == x@` through the mutating-call lane. It
//@ mechanism: holds only where the arm ran; unscoped, `ensures(x@ < 100)` follows on the `!flag` path.
//@ accept-means: a contract is verified from a callee postcondition on an execution that never calls it,
//@ accept-means: and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false, 0)` returns with `x == 200`.
//@ teeth: ACCEPTED at the campaign tip; rejected with D-169.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: set_below
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100 && (^r)@ == x@)]
pub fn set_below(r: &mut u32, x: u32) {
    #[invariant(true)]
    while x >= 100 {}
    *r = x;
}

#[ensures(x@ < 100)]
pub fn f(x: u32, flag: bool, mut y: u32) {
    if flag { set_below(&mut y, x); }
}
