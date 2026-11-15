//@ expect: reject
//@ mechanism: Creusot's `such_that(p)` requires that a witness of `p` exists, which the walk cannot state; the call is refused (`STD_UNSTATED_PRECONDITIONS`) where the encoder would read it as a placeholder.
//@ accept-means: a logic function that picks a witness of an empty predicate is credited `verified`.
//@ WHY IT IS FALSE: no `y` satisfies `y != y`, so `such_that`'s precondition fails wherever the body is evaluated.
//@ teeth: MEASURED on the commit before D-119: nothing examined (`proved, not credited`, exit 2). With the lane crediting a function with no `ensures` but no standard-library refusal, `caller verified ✓`.
//@ fixed-by: D-119
//@ verdict: unknown
//@ refused-with: to a standard logic function whose precondition the logic lane cannot state
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
    creusot_std::logic::such_that(|y: Int| y != y)
}
