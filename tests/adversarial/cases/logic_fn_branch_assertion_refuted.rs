//@ expect: reject
//@ mechanism: a logic function's assertion inside one arm of an `if` is owed under that arm's condition only; the goal the logic lane states keeps the branch (`logic_fn_verify::assertions::goal_of`). This case pins that the arm's assertion is examined at all.
//@ accept-means: an assertion false at `x == 1`, which reaches it, is never examined.
//@ WHY THE ASSERTION IS FALSE: at `x == 1` the first arm is taken and `1 >= 2` fails.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `creusot_test::f verified ✓` with no assertion verdict.
//@ fixed-by: D-106
//@ fn-failed: creusot_test::f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result >= 0)]
pub fn f(x: Int) -> Int {
    if x > 0 {
        proof_assert!(x >= 2);
        x
    } else {
        0
    }
}
