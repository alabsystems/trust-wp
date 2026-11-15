//@ expect: reject
//@ mechanism: the termination lane printed `verified ✓ (termination)` (and the function-level VC a second `verified ✓`) before the in-body assertion pass ran, so a recursive function whose own `proof_assert!` was refuted was counted verified twice
//@ accept-means: a recursive function is credited on a VC that omits its own assertion goal.
//@ WHY THE ASSERTION IS FALSE: the branch is reached with n == 0, where n < 0 does not hold.
//@ verdict: failed
//@ fn-failed: rec_zero
//@ teeth: MEASURED on the parent commit, TEETH LOST: the run printed `verified ✓ (termination)` and `verified ✓` beside the FAILED assertion and summed `2 verified, 0 failed` for one function (s80_rec_selfspec_result_leak.rs is the same shape). The twin `own_assertion_termination_lane_control.rs` differs only in the comparison.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn rec_zero(n: i32) -> i32 {
    if n <= 0 {
        proof_assert!(n < 0i32);
        0
    } else {
        rec_zero(n - 1)
    }
}
