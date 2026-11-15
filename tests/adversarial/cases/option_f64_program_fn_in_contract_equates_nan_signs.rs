//@ expect: reject
//@ ay-not-unsat: same
//@ mechanism: the float model has one NaN where Rust has many (a sign bit and a payload), so a
//@ mechanism: contract's logical `a == b` holds of `Some(f64::NAN)` and `Some(-f64::NAN)`. A program
//@ mechanism: function a contract applies is read as an uninterpreted function of the model value, and
//@ mechanism: congruence then equates `neg_sign(a)` with `neg_sign(b)`, which `is_sign_negative` tells
//@ mechanism: apart. ay proves the false postcondition; only the sort-fallback demotion of the Int-carried
//@ mechanism: `Option` argument, which is no float guard, withholds the credit.
//@ accept-means: `same(Some(f64::NAN), Some(-f64::NAN))` meets the precondition, and `neg_sign` returns
//@ accept-means: `false` for the first argument and `true` for the second; an accept claims they agree.
//@ fixed-by: OPEN
//@ teeth: RED when committed: ay answers unsat on `same`, printed `unknown (demoted: ... sort_fallback_to_int_from_logic_fn)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn neg_sign(a: Option<f64>) -> bool {
    match a {
        Some(x) => x.is_sign_negative(),
        None => false,
    }
}

#[requires(a == b)]
#[ensures(neg_sign(a) == neg_sign(b))]
pub fn same(a: Option<f64>, b: Option<f64>) {}
