//@ expect: verify
//@ mechanism: the control of loop_entry_reads_if_join_as_one_arm_value.rs: the invariant holds for the value of
//@ mechanism: either arm, so the entry value the block-slice walker states (a join symbol defined arm by arm,
//@ mechanism: D-243) initiates it.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool) {
    let m = if c { 1u32 } else { 2u32 };
    let mut i = 0u32;
    #[invariant(m >= 1u32 && m <= 2u32)]
    while i < 3 {
        i += 1;
    }
}
