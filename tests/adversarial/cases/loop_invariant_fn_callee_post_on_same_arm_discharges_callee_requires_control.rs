//@ expect: verify
//@ mechanism: the control of loop_invariant_fn_callee_post_on_other_arm_discharges_callee_requires.rs: `need_small`
//@ mechanism: is called on the arm that calls `below`, so its goal, owed under `flag`, is discharged by the premise
//@ mechanism: stated under `flag`.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[requires(x@ < 100)]
pub fn need_small(x: u32) {}

pub fn f(x: u32, flag: bool) {
    if flag {
        below(x);
        need_small(x);
    }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
