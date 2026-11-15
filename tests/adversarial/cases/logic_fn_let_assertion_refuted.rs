//@ expect: reject
//@ mechanism: a logic function's assertion over a `let`-bound name is owed with the binding in scope (`logic_fn_verify::assertions::goal_of` keeps it); this case pins that such an assertion is examined and refuted.
//@ accept-means: an assertion false for every argument is never examined, and the function is credited on its true `ensures`.
//@ WHY THE ASSERTION IS FALSE: `y` is `x + 1`, never `x + 2`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `creusot_test::f verified ✓` with no assertion verdict.
//@ fixed-by: D-106
//@ fn-failed: creusot_test::f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result == x + 1)]
pub fn f(x: Int) -> Int {
    let y = x + 1;
    proof_assert!(y == x + 2);
    y
}
