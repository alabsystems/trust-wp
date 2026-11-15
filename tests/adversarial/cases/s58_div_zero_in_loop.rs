//@ expect: reject
//@ mechanism: a division inside an annotated loop body: the divisor obligation is owed under
//@ mechanism: the loop invariant at the loop-body program point, not skipped with the body.
//@ fixed-by: 8235a110 (machine-int arithmetic panics are proof obligations) + 81e7dee8
//@ accept-means: an arithmetic panic site inside a loop body owes no divisor obligation.
//@ WHY THE PROGRAM IS WRONG: `f(1, 0)` enters the loop once and panics (divide by zero).
//@ teeth: verified — ACCEPTED on a local mutant whose DivisionByZero/RemainderByZero arm of
//@ teeth: `build_arithmetic_panic_obligation` yields `true` (exactly the handed-on "owes no
//@ teeth: obligation of its own" defect); measured wp-s58 2026-09-14. NOT accepted at campaign
//@ teeth: 03a35447 — the handed-on s53 report did not reproduce there.
//@ teeth: The quotient is loop-carried, so trust-wp-ay's encoder-side divisor obligation does
//@ teeth: not reach it; the driver-side loop-body lane is the only one that owes the check here.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(d@ != -1)]
#[ensures(true)]
pub fn f(n: u32, d: i32) -> i32 {
    let mut s = 0i32;
    let mut i: u32 = 0;
    #[invariant(i <= n)]
    while i < n {
        s = 10i32 / d;
        i += 1;
    }
    s
}
