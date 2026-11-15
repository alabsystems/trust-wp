//@ expect: verify
//@ mechanism: the control of program_ensures_reads_if_join_past_loop_as_one_arm_value.rs: the postcondition holds
//@ mechanism: for either arm's value, which the loop leaves alone; the block-slice walker states `m` at the loop's
//@ mechanism: entry as a join symbol and nothing changes it after (D-243).
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result >= 1u32 && result <= 2u32)]
pub fn f(c: bool) -> u32 {
    let m = if c { 1u32 } else { 2u32 };
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
    m
}
