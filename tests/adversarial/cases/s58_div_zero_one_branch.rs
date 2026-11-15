//@ expect: reject
//@ mechanism: the divisor is zero only on one arm of a branch: the obligation must be stated
//@ mechanism: under that arm's path condition, not discharged by the sibling arm.
//@ fixed-by: 8235a110 (machine-int arithmetic panics are proof obligations) + 81e7dee8
//@ accept-means: a branch-guarded division site owes no divisor obligation.
//@ WHY THE PROGRAM IS WRONG: `f(true, 0)` is an admitted call and panics (divide by zero);
//@ WHY THE PROGRAM IS WRONG: the `else` arm divides by the literal 2 and is fine.
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
pub fn f(b: bool, d: i32) {
    if b {
        let _z = 10i32 / d;
    } else {
        let _z = 10i32 / 2i32;
    }
}
