//@ expect: reject
//@ mechanism: a recursive logic function's call to ITSELF owes its own precondition at the call's arguments (Creusot's vcgen `Call` makes no exception for the function being defined). The variant check at extraction proves only that `x - 2` decreases, and the `ensures` holds whatever the recursive call returns, so the ensures lane credits the function: nothing examined the call.
//@ accept-means: a recursive logic function that calls itself outside its precondition is credited `verified`.
//@ WHY IT IS FALSE: at `x == 2`, which `x > 0` admits, the body calls `f(0)`, and `f` requires `0 > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::f verified ✓`, the call never examined.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
#[ensures(true)]
#[variant(x)]
pub fn f(x: Int) -> Int {
    if x > 1 {
        f(x - 2)
    } else {
        0
    }
}
