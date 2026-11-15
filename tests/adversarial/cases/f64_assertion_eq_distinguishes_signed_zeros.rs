//@ expect: reject
//@ mechanism: an assertion's `==` is logical equality (D-215), under which `-0.0` and `0.0` are
//@ mechanism: different values; the program's `==` on the same operands is IEEE-754 and equates them
//@ mechanism: (f64_program_eq_equates_signed_zeros_control.rs). The two cases differ only in where
//@ mechanism: `z == 0.0` is written. Reals have one zero and read both as the same claim.
//@ accept-means: `z` is `-0.0`; an accept claims the assertion that it is the value `0.0` holds.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`proof_assert in creusot_test::assertion_zeros_equal verified`) on the campaign
//@ teeth: tip before D-215, which read both zeros as the real 0; rejected after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn assertion_zeros_equal() {
    let z = -0.0f64;
    proof_assert!(z == 0.0);
}
