//@ expect: reject
//@ mechanism: an arm walk's premises are scoped to its edge (D-169). Here the callee `below(x)` runs on the
//@ mechanism: `flag` arm and its RESULT flows out of the `if` as the function's result
//@ mechanism: (`Ite(flag, $call, x)`). Its postcondition `x@ < 100` holds only where the arm ran; unscoped,
//@ mechanism: it is a premise of the `!flag` path too, where the result is `x` itself, and
//@ mechanism: `ensures(result@ < 100)` follows.
//@ accept-means: a function whose result is its argument on one path is verified against a bound only the
//@ accept-means: other path establishes, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false)` returns 200.
//@ teeth: ACCEPTED at the campaign tip, and ACCEPTED with `guard_branch_assumptions` made a no-op on
//@ teeth: this branch (its control still verifies); rejected with D-169.
//@ verdict: failed
//@ fn-failed: f
//@ also-verified: below
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

#[ensures(result@ < 100)]
pub fn f(x: u32, flag: bool) -> u32 {
    if flag { below(x) } else { x }
}
