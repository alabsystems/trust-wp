//@ expect: reject
//@ also-verified: need, need_zero
//@ mechanism: a program float comparison's outcome discharges an obligation in three lanes other than the
//@ mechanism: postcondition: a callee's precondition (`need(x == x)`), a loop invariant's initialization
//@ mechanism: (`let b = x == x;` then `#[invariant(b)]`) and a type invariant at construction
//@ mechanism: (`Checked { v: x, ok: x == x }`). Over the reals `x == x` is true; over IEEE-754 it is
//@ mechanism: false at NaN. `zero_path` takes the arm `x == 0.0`, which IEEE also takes at `-0.0`, and
//@ mechanism: passes `x` to a callee whose precondition `x == 0.0` is logical equality (D-215 point 5),
//@ mechanism: false of `-0.0`. i64_comparison_outcome_meets_callee_and_invariant_obligations_control.rs
//@ mechanism: is the same bodies over `i64`. `need` and `need_zero` are true and credited.
//@ accept-means: `call_arg(f64::NAN)` calls `need(false)`; `loop_init(f64::NAN)` enters the loop with its
//@ accept-means: invariant false; `type_inv(f64::NAN)` returns a `Checked` whose invariant is false;
//@ accept-means: `zero_path(-0.0)` calls `need_zero(-0.0)`, whose precondition is false.
//@ fixed-by: D-215
//@ teeth: ACCEPTED at the merged campaign tip before D-215 (`call_arg`, `loop_init`, `type_inv` and
//@ teeth: `zero_path` each verified: the reals read `x == x` as true and the arm `x == 0.0` as the logical
//@ teeth: zero); under D-215 each is `unknown`, ay answering `unknown` or `sat` (the loop invariant's
//@ teeth: initialization gets a counterexample), never `unsat`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(b)]
pub fn need(b: bool) {}

#[ensures(result == 1i32)]
pub fn call_arg(x: f64) -> i32 {
    need(x == x);
    1
}

#[ensures(result == 3i32)]
pub fn loop_init(x: f64) -> i32 {
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
    pub v: f64,
    pub ok: bool,
}

impl Invariant for Checked {
    #[logic(open)]
    fn invariant(self) -> bool {
        self.ok
    }
}

#[ensures(result.v == x)]
pub fn type_inv(x: f64) -> Checked {
    Checked { v: x, ok: x == x }
}

#[requires(x == 0.0)]
pub fn need_zero(x: f64) {}

#[ensures(result == 1i32)]
pub fn zero_path(x: f64) -> i32 {
    if x == 0.0 {
        need_zero(x);
    }
    1
}
