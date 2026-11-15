//@ expect: reject
//@ ay-not-unsat: same
//@ mechanism: the float model has one NaN where Rust has many (a sign bit and a payload), so a
//@ mechanism: contract's logical `x == y` holds of `f64::NAN` and `-f64::NAN`. A program function a
//@ mechanism: contract applies to a float is read as an uninterpreted function of the model value, and
//@ mechanism: congruence then equates `sign(x)` with `sign(y)`, which `is_sign_negative` tells apart. The
//@ mechanism: direct-float twin of option_f64_program_fn_in_contract_equates_nan_signs.rs.
//@ accept-means: `same(f64::NAN, -f64::NAN)` meets the precondition, and `sign` returns `false` for the
//@ accept-means: first argument and `true` for the second; an accept claims they agree.
//@ fixed-by: OPEN
//@ teeth: UNVERIFIED: rejected when committed only because ay answers unknown on `same` (it does not decide
//@ teeth: a floating-point variable under congruence); `ay-not-unsat` fails the case the day it answers unsat.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn sign(x: f64) -> bool {
    x.is_sign_negative()
}

#[requires(x == y)]
#[ensures(sign(x) == sign(y))]
pub fn same(x: f64, y: f64) {}
