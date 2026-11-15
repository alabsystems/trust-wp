//@ expect: reject
//@ mechanism: the function-level VC printed `verified ✓` for a function before its in-body assertion pass ran, so a function whose own `proof_assert!` was refuted in the same run was reported and counted verified (`1 verified, 0 failed`)
//@ accept-means: a function is credited on a VC that omits its own assertion goal. Creusot puts a `proof_assert!` in the VC of the function it sits in.
//@ WHY THE ASSERTION IS FALSE: y is x + 1, never x + 2; x = 0 refutes it.
//@ verdict: failed
//@ fn-failed: add_one
//@ teeth: MEASURED on the parent commit, TEETH LOST: the run printed `add_one verified ✓` beside `proof_assert in creusot_test::add_one FAILED ✗` and summed `1 verified, 0 failed`; `fn-failed` is what the old output lacked. The twin `own_assertion_function_lane_control.rs` differs only in the literal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result@ == x@ + 1)]
pub fn add_one(x: u32) -> u32 {
    let y = x + 1;
    proof_assert!(y@ == x@ + 2);
    y
}
