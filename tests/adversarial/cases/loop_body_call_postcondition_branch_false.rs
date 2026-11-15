//@ expect: reject
//@ mechanism: reject twin of loop_body_call_postcondition_branch_control: the arm WITHOUT the call
//@ mechanism: stores 7. A postcondition stated for every path, rather than for the arm that makes
//@ mechanism: the call, would hide that arm.
//@ accept-means: `go(1)` stores 7 into `x` on its first iteration, so `x != 7u32` is FALSE after
//@ accept-means: it, and trust-wp proved the invariant preserved.
//@ verdict: failed
//@ fn-failed: go
//@ also-verified: below
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result < 7u32)]
pub fn below() -> u32 { 0 }

pub fn go(n: u32) {
    let mut i: u32 = 0;
    let mut x: u32 = 5;
    #[invariant(x != 7u32)]
    while i < n {
        if i == 0u32 { x = 7; } else { x = below(); }
        i += 1;
    }
}
