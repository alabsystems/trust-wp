//@ expect: reject
//@ mechanism: an arm premise in a recursive function with a variant (D-169): the base case `n == 0` calls
//@ mechanism: `below(x)` only when `flag`. The recursive call's postcondition is the inductive hypothesis
//@ mechanism: on the `n > 0` arm; neither it nor `below`'s postcondition may reach the `n == 0 && !flag` path.
//@ accept-means: a recursive function is verified against a contract its base case violates, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false, 0)` returns with `x == 200`.
//@ teeth: ACCEPTED at the campaign tip; rejected with D-169.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below, f
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100 && result == x)]
pub fn below(x: u32) -> u32 {
    #[invariant(true)]
    while x >= 100 {}
    x
}

#[variant(n@)]
#[ensures(x@ < 100)]
pub fn f(x: u32, flag: bool, n: u32) {
    if n > 0 { f(x, flag, n - 1) } else if flag { below(x); }
}
