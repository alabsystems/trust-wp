//@ expect: verify
//@ mechanism: the control of loop_invariant_fn_callee_post_past_dead_end_arm_discharges_callee_requires.rs:
//@ mechanism: `need_small` follows `below` on the path that reaches it, so the premise `x@ < 100`, stated where
//@ mechanism: `below` runs, discharges the goal owed there.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
pub fn need_small(x: u32) {}

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

pub fn f(x: u32, c: bool, d: bool) {
    if c {
        if d {
            #[invariant(true)]
            loop {}
        }
    }
    below(x);
    need_small(x);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
