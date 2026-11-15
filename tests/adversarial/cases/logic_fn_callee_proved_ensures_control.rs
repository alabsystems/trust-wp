//@ expect: verify
//@ mechanism: control for logic_fn_callee_unproved_ensures_credits_caller.rs: the same chain with `g`'s body `x + 1` in place of `h(x)`, so every claim holds and `f` rests on a proved `ensures`.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@ teeth: n/a — over-refusal control for the neutralization of lost callees in the logic pass.
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
pub fn g(x: Int) -> Int {
    x + 1
}

#[logic]
#[ensures(result > x)]
pub fn f(x: Int) -> Int {
    g(x)
}

#[ensures(f(0int) > 0)]
pub fn p() {}
