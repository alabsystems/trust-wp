//@ expect: verify
//@ mechanism: control for logic_fn_callee_declared_after_caller_unproved.rs: `g`'s body is `x + 1` in place of `h(x)`, so nothing is lost after `f`'s proof and its credit stands.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@ teeth: n/a — over-refusal control for the withdrawal of stale logic credits.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(opaque)]
pub fn h(x: Int) -> Int {
    x
}

#[logic]
#[ensures(result > x)]
pub fn f(x: Int) -> Int {
    g(x)
}

#[logic]
#[ensures(result > x)]
pub fn g(x: Int) -> Int {
    x + 1
}

#[ensures(f(0int) > 0)]
pub fn p() {}
