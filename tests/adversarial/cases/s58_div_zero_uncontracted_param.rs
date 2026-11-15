//@ expect: reject
//@ mechanism: the divisor is a parameter with no precondition, so `divisor != 0` is not
//@ mechanism: derivable at the division's program point.
//@ fixed-by: 8235a110 (machine-int arithmetic panics are proof obligations) + 81e7dee8
//@ accept-means: a primitive `/` is credited with no divisor obligation at all.
//@ WHY THE PROGRAM IS WRONG: `f(1, 0)` is an admitted call and panics (divide by zero).
//@ teeth: verified — ACCEPTED on a local mutant whose DivisionByZero/RemainderByZero arm of
//@ teeth: `build_arithmetic_panic_obligation` yields `true` (exactly the handed-on "owes no
//@ teeth: obligation of its own" defect); measured wp-s58 2026-09-14. NOT accepted at campaign
//@ teeth: 03a35447 — the handed-on s53 report did not reproduce there.
//@ teeth: The quotient is DISCARDED on purpose: when it reaches the goal, trust-wp-ay's own
//@ teeth: encoder-side divisor obligation refutes the case independently, and the driver-side
//@ teeth: lane this case gates would not be the deciding one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(d@ != -1)]
#[ensures(true)]
pub fn f(n: i32, d: i32) {
    let _z = n / d;
}
