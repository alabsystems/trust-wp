//@ expect: verify
//@ mechanism: the control of pre_loop_if_value_read_by_callee_requires_at_one_arm_value.rs: `need_pos` holds for the
//@ mechanism: value of either arm, so the join symbol, defined arm by arm, discharges it.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k > 0u32)]
pub fn need_pos(k: u32) {}

pub fn f(c: bool) {
    let m = if c { 1u32 } else { 2u32 };
    need_pos(m);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
