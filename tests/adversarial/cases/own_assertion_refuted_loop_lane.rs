//@ expect: reject
//@ mechanism: the loop lane owns the verdict of a function with no postcondition and printed `verified ✓ (loop invariant)` before the in-body assertion pass ran, so a function whose own `proof_assert!` after the loop was refuted was still counted verified
//@ accept-means: a loop-lane function is credited on a VC that omits its own assertion goal.
//@ WHY THE ASSERTION IS FALSE: the loop exits with i == n, never n + 1; n = 0 refutes it.
//@ verdict: failed
//@ fn-failed: count_up
//@ teeth: MEASURED on the parent commit, TEETH LOST: the run printed `count_up verified ✓ (loop invariant + call obligations)` beside the FAILED assertion and summed `1 verified`. The gate then read that spelling as a lane report and flagged nothing, so `fn-failed` carried the teeth; it now reads a lane credit beside an unproved own assertion as contradicted too. The twin `own_assertion_loop_lane_control.rs` differs only in the literal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ < 1000)]
pub fn count_up(n: u32) {
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        i += 1;
    }
    proof_assert!(i@ == n@ + 1);
}
