//@ expect: verify
//@ mechanism: the control of pre_loop_branch_join_read_by_callee_requires_at_one_arm_value.rs: both arms leave
//@ mechanism: `i == 7`, so the join binds `i` to the value both predecessors agree on and `need7(i)` is owed `7 == 7`.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 7u32)]
pub fn need7(k: u32) {}

pub fn go(c: bool) {
    let mut n = 0u32;
    let mut i = 7u32;
    if c {
        n = 1;
    } else {
        i = 7;
    }
    need7(i);
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
}
