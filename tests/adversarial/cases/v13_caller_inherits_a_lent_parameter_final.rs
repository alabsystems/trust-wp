//@ expect: reject
//@ mechanism: v12_caller_inherits_a_lent_parameter_resolve spelled with `^x == *x` instead of
//@ mechanism: `resolve(x)`. The callee's own lane refutes the claim, but a call reads the callee's
//@ mechanism: postcondition over the final value the caller's lane names for the argument's borrow, and
//@ mechanism: the caller was credited over that refuted contract: `a`'s final value is pinned to its
//@ mechanism: value at the call, and `opaque(r)` (contract `true`) cannot contradict it.
//@ accept-means: `exploit` is credited with `result == 3` although it returns 5, over a callee
//@ accept-means: contract its own lane refutes.
//@ WHY THE CONTRACT IS FALSE: `lend` hands `x` to its caller in the returned borrow, and the caller
//@ WHY THE CONTRACT IS FALSE: writes 5 through it (`opaque`), so `^x != *x`, and `exploit` returns 5.
//@ fixed-by: D-127 (a credit rests on the own contract of every local callee it names; one its own
//@ fixed-by: verification did not discharge withdraws it)
//@ teeth: MEASURED (debug driver): before D-127 `lend` and `lend_reborrow` FAILED and `exploit`,
//@ teeth: `exploit_reborrow`, `exploit_inner` and `through_a_wrapper` (which rests on `lend` only
//@ teeth: through `exploit_inner`) verified (TEETH LOST); D-127 withdraws all four callers.
//@ also-verified: opaque
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn lend(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(^x == *x)]
pub fn lend_reborrow(x: &mut i32) -> &mut i32 {
    &mut *x
}

#[ensures(true)]
pub fn opaque(x: &mut i32) {
    *x = 5;
}

#[ensures(result == 3i32)]
pub fn exploit() -> i32 {
    let mut a = 3i32;
    let r = lend(&mut a);
    opaque(r);
    a
}

#[ensures(result == 3i32)]
pub fn exploit_reborrow() -> i32 {
    let mut a = 3i32;
    let r = lend_reborrow(&mut a);
    opaque(r);
    a
}

#[ensures(result == 3i32)]
fn exploit_inner() -> i32 {
    let mut a = 3i32;
    let r = lend(&mut a);
    opaque(r);
    a
}

#[ensures(result == 3i32)]
pub fn through_a_wrapper() -> i32 {
    exploit_inner()
}
