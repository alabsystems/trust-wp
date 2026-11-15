//@ expect: verify
//@ mechanism: the control of loop_invariant_fn_post_loop_callee_post_on_other_arm.rs: the panic switch sits on the
//@ mechanism: arm that calls `below`, so the premise `x@ < 100`, scoped to `flag`, discharges the goal owed under `flag`.
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

#[ensures(true)]
pub fn f(x: u32, flag: bool) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    if flag {
        below(x);
        if x >= 100 {
            panic!()
        }
    }
}
