//@ expect: reject
//@ mechanism: reject twin of loop_condition_call_own_precondition_control: `small` requires `k < 10`,
//@ mechanism: and the header calls it once more at `i == 10` to leave the loop. The precondition is
//@ mechanism: owed BEFORE the switch, so the condition the call computes may not discharge it: a
//@ mechanism: check that assumed the condition would read `i < 10` out of the call's own result.
//@ accept-means: `go()` calls `small(10)` outside its precondition, and trust-wp proved every call
//@ accept-means: precondition.
//@ verdict: failed
//@ fn-failed: go
//@ also-verified: small
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k < 10u32)]
#[ensures(result == (k < 10u32))]
pub fn small(k: u32) -> bool { k < 10 }

pub fn go() {
    let mut i = 0u32;
    #[invariant(i <= 10u32)]
    while small(i) { i += 1; }
}
