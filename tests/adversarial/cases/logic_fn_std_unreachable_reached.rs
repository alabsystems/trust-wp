//@ expect: reject
//@ mechanism: Creusot's `logic::unreachable` requires `false`; the encoder reads the call as an unconstrained value. The walk owes `false` where the call is reached (`std_logic_precondition`).
//@ accept-means: a requires-only logic function that reaches `unreachable()` is credited `verified` on a true assertion.
//@ WHY IT IS FALSE: at `x == 0` the body reaches `unreachable()`, whose precondition is `false`.
//@ teeth: MEASURED on the commit before D-119: nothing examined (`proved, not credited`, exit 2). With the lane crediting a function with no `ensures` but no standard-library preconditions owed, `caller verified ✓`.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::caller
//@ also-verified-assertion: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(true)]
pub fn caller(x: Int) -> Int {
    proof_assert!(true);
    if x > 0 { 0 } else { creusot_std::logic::unreachable() }
}
