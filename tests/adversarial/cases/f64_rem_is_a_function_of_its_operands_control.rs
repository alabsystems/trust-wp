//@ expect: verify
//@ mechanism: the control for f64_rem_refused_value_meets_callee_precondition.rs: a float `%` over
//@ mechanism: parameters is an uninterpreted function of its two operands (D-215), so two evaluations
//@ mechanism: of `a % b` are one value, and neither is the entry value of an operand. The precondition
//@ mechanism: pins both operands to non-NaN values, so the claim holds of Rust's own remainder too.
//@ accept-means: n/a (control) — `caller(7.0, 2.0)` passes `1.0` twice.
//@ fixed-by: n/a (control)
//@ teeth: verified on the campaign tip before D-215 (the remainder over the reals); `caller` and `caller_f32`
//@ teeth: failed while D-215 left `%` untranslated; verified with `%` an uninterpreted function of its operands.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x == y)]
pub fn needs_same(x: f64, y: f64) {}

#[requires(a == 7.0 && b == 2.0)]
#[ensures(true)]
pub fn caller(a: f64, b: f64) {
    needs_same(a % b, a % b);
}

#[requires(a == 7.0f32 && b == 2.0f32)]
#[ensures(true)]
pub fn caller_f32(mut a: f32, b: f32) {
    let c = a;
    a %= b;
    needs_same_f32(a, c % b);
}

#[requires(x == y)]
pub fn needs_same_f32(x: f32, y: f32) {}
