//@ expect: reject
//@ mechanism: requires o.is_none() then o.unwrap().
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ accept-means: the unwrap requires is no longer emitted at the call site.
//@ WHY THE PROGRAM IS WRONG: unwrap on None panics.
//@ teeth: rejected only as unknown (quantifier-unhandled) on b98d5d87; the s43 v2 review saw it verify with exit 0 on an earlier build.
//@ teeth: the call-site obligation IS emitted (--emit-smt-dir goal `(assert (not (and true (is_some o))))` under `(assert (is_none o))`, wp-s48 1229a3db); the
//@ teeth: verdict stays unknown only because ay cannot model-validate SAT under the Option axioms.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(o.is_none())] #[ensures(true)] pub fn f(o: Option<i32>) -> i32 { o.unwrap() }
