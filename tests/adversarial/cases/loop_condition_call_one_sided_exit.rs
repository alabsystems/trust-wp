//@ expect: reject
//@ mechanism: a loop condition that calls a function whose contract is one-sided. `pos` promises only
//@ mechanism: `result ==> k > 0u32`, so at the exit, where the condition is false, nothing bounds `i`
//@ mechanism: but the invariant. Each evaluation of the condition is its own symbol with the clause
//@ mechanism: stated at it as written: reading the clause as `result == (k > 0u32)`, or letting the
//@ mechanism: exit's evaluation share the body's (where it is true), proves the exit value is 0.
//@ accept-means: `h(3)` returns 3 (`pos(3)` is false at once), so `ensures(result == 0u32)` is FALSE,
//@ accept-means: and trust-wp proved it.
//@ teeth: UNVERIFIED as a false-accept gate: rejected on every build measured. Before
//@ teeth: D-222, the rejection was a FALSE refutation of the true invariant `i <= n` at preservation
//@ teeth: (the condition read a placeholder no clause described, so the model entered the body where
//@ teeth: `pos` rules it out); `refused-with:` pins the postcondition as the refuted claim. loop_condition_call_one_sided_exit_control is the
//@ teeth: isolating twin.
//@ verdict: failed
//@ fn-failed: h
//@ refused-with: h FAILED ✗ (postcondition)
//@ also-verified: pos
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result ==> k > 0u32)]
pub fn pos(k: u32) -> bool { k > 3 }

#[requires(n < 50u32)]
#[ensures(result == 0u32)]
pub fn h(n: u32) -> u32 {
    let mut i = n;
    #[invariant(i <= n)]
    while pos(i) { i -= 1; }
    i
}
