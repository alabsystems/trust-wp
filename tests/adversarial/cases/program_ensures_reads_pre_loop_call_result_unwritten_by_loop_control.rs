//@ expect: verify
//@ mechanism: the control of program_ensures_reads_pre_loop_call_result_assigned_in_loop.rs: the loop does not
//@ mechanism: write `k`, directly or through a loan, so `zero`'s postcondition about `k` stays a premise after it.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn zero() -> u32 {
    0
}

#[ensures(result == 0u32)]
pub fn go() -> u32 {
    let mut m = 0u32;
    let k = zero();
    #[invariant(m <= 3u32)]
    while m < 3 {
        m += 1;
    }
    k
}
