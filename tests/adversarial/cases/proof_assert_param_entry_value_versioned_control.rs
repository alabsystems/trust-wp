//@ expect: verify
//@ mechanism: control for the by-value parameter entry/current versioning (D-241): a scalar parameter
//@ mechanism: the body re-binds keeps its `#[requires]` as a fact about its ENTRY value, which a copy
//@ mechanism: taken before the write, the written value (`x = x + 1`), a branch's merge and a callee's
//@ mechanism: postcondition over the argument as it was passed all read. Withdrawing the entry fact of
//@ mechanism: a re-bound parameter (D-140) refuted or left vacuous every one of these TRUE claims but
//@ mechanism: `copy_keeps`, which it proved only by reading the copy at the value written after it.
//@ accept-means: n/a (control) — every claim here holds in every execution.
//@ fixed-by: n/a (control)
//@ teeth: on D-240 (no versioning) `inc_keeps`, `copy_then_inc`, `call_after` and `two_params` are
//@ teeth: `unknown` (vacuous: `x == x + 1`), `branch_write` and `call_before` FAILED; all verified with D-241.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn id(a: u32) -> u32 {
    a
}

#[requires(x@ > 0)]
pub fn copy_keeps(mut x: u32) {
    let y = x;
    x = 5;
    proof_assert!(y@ > 0);
    let _ = x;
}

#[requires(x@ < 10)]
pub fn inc_keeps(mut x: u32) {
    x = x + 1;
    proof_assert!(x@ < 11);
}

#[requires(x@ < 10)]
pub fn copy_then_inc(mut x: u32) {
    let y = x;
    x = x + 1;
    proof_assert!(x@ == y@ + 1);
    proof_assert!(y@ < 10);
}

#[requires(x@ < 10)]
pub fn branch_write(mut x: u32, c: bool) {
    if c {
        x = 3;
    }
    proof_assert!(x@ < 10);
}

#[requires(x@ == 0)]
pub fn call_after(mut x: u32) {
    x = x + 1;
    let r = id(x);
    proof_assert!(r@ == 1);
}

#[requires(x@ == 0)]
pub fn call_before(mut x: u32) {
    let r = id(x);
    x = 5;
    proof_assert!(r@ == 0);
    let _ = x;
}

#[requires(x@ < 10 && y@ < 10)]
pub fn swap_values(mut x: u32, mut y: u32) {
    let a = x;
    let b = y;
    let t = x;
    x = y;
    y = t;
    proof_assert!(x == b && y == a);
    proof_assert!(x@ < 10 && y@ < 10);
}

#[requires(x@ < y@)]
pub fn two_params(mut x: u32, y: u32) {
    x = x + 1;
    proof_assert!(x@ <= y@);
}

#[requires(x@ == 0)]
pub fn self_assign(mut x: u32) {
    let y = x;
    x = y;
    proof_assert!(x@ == 0);
}
