//@ expect: reject
//@ also-verified: needs_one
//@ mechanism: the call-precondition sink of f64_rem_assign_reads_param_as_unchanged.rs. A float `%` left
//@ mechanism: untranslated binds its destination to `Var(<source name>)`, for a parameter its entry
//@ mechanism: symbol: after `a %= 0.5` the argument of `needs_one(a)` is read as the entry `a`, which the
//@ mechanism: caller's precondition makes `1.0`, so the callee's precondition is discharged against a
//@ mechanism: value the program no longer holds. The `f32` and two-literal spellings reach the same
//@ mechanism: fallback unless `%` is folded on the host. `needs_one` is true and is credited.
//@ accept-means: `rem_then_call(1.0)` calls `needs_one(0.0)`, whose precondition is false; `rem_f32(7.0, 5.0)`
//@ accept-means: returns `2.0`, not `7.0`; `literal_rem(1.0)` returns `2.0`, not `1.0`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED while D-215 left `%` untranslated (`rem_then_call`, `rem_f32` and `literal_rem` each
//@ teeth: verified); each `unknown` on the campaign tip before D-215, which translated the remainder over
//@ teeth: the reals; each FAILED with `%` an uninterpreted function and a two-literal `%` folded.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x == 1.0)]
pub fn needs_one(x: f64) -> f64 {
    x
}

#[requires(a == 1.0)]
pub fn rem_then_call(mut a: f64) -> f64 {
    a %= 0.5;
    needs_one(a)
}

#[ensures(result == a)]
pub fn rem_f32(mut a: f32, y: f32) -> f32 {
    a %= y;
    a
}

#[ensures(result == x)]
pub fn literal_rem(x: f64) -> f64 {
    let x = 7.0f64 % 5.0;
    x
}
