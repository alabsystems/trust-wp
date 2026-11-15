//@ expect: verify
//@ mechanism: control for own_assertion_refuted_termination_lane.rs: the same recursive function with a TRUE assertion keeps both its termination and its function-level credit
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn rec_zero(n: i32) -> i32 {
    if n <= 0 {
        proof_assert!(n <= 0i32);
        0
    } else {
        rec_zero(n - 1)
    }
}
