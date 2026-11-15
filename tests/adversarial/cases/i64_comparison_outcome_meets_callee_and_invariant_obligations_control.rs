//@ expect: verify
//@ mechanism: the integer twin of f64_comparison_outcome_meets_callee_and_invariant_obligations.rs: over
//@ mechanism: `i64`, `x == x` is true and `x == 0` taken as a path condition is the callee's precondition,
//@ mechanism: so each obligation is discharged by what the program computed.
//@ accept-means: n/a (control) — every integer equals itself, and `x == 0` is one value.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215 (each function verified).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(b)]
pub fn need(b: bool) {}

#[ensures(result == 1i32)]
pub fn call_arg(x: i64) -> i32 {
    need(x == x);
    1
}

#[ensures(result == 3i32)]
pub fn loop_init(x: i64) -> i32 {
    let b = x == x;
    let mut i = 0i32;
    #[invariant(b)]
    #[invariant(i <= 3i32)]
    while i < 3i32 {
        i += 1;
    }
    i
}

pub struct Checked {
    pub v: i64,
    pub ok: bool,
}

impl Invariant for Checked {
    #[logic(open)]
    fn invariant(self) -> bool {
        self.ok
    }
}

#[ensures(result.v == x)]
pub fn type_inv(x: i64) -> Checked {
    Checked { v: x, ok: x == x }
}

#[requires(x == 0i64)]
pub fn need_zero(x: i64) {}

#[ensures(result == 1i32)]
pub fn zero_path(x: i64) -> i32 {
    if x == 0 {
        need_zero(x);
    }
    1
}
