//@ expect: reject
//@ mechanism: `%` on machine integers emits a MIR Assert(RemainderByZero); the same
//@ mechanism: `divisor != 0` obligation is owed at its own program point.
//@ fixed-by: 8235a110 (machine-int arithmetic panics are proof obligations) + 81e7dee8
//@ accept-means: the RemainderByZero arm owes nothing, so every primitive `%` is credited.
//@ WHY THE PROGRAM IS WRONG: `n - n` is 0 for every i32 `n`; `10 % 0` panics on every execution.
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

#[ensures(true)]
pub fn g(n: i32) {
    let _z = 10i32 % (n - n);
}
