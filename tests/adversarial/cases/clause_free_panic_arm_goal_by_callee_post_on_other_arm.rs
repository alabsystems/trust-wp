//@ expect: reject
//@ mechanism: D-142 reads a switch edge as dead when the walk's charge that the arm is not taken is
//@ mechanism: proved. `below(x)` runs only when `flag` holds, but the primary walk records its
//@ mechanism: postcondition `x@ < 100` unguarded by `flag`, as a premise of every goal; the charge
//@ mechanism: `!(x >= 100)` owed on the `!flag` path is then proved from it.
//@ accept-means: a clause-free body that panics on the path that skips the call is credited
//@ accept-means: `verified`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false)` panics (a clause-free fn is checked under `requires true`).
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

pub fn f(x: u32, flag: bool) {
    if flag {
        below(x);
    }
    if x >= 100 {
        panic!()
    }
}
