//@ expect: reject
//@ mechanism: checked_div(0) returns None, so unwrap panics.
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ accept-means: the unwrap requires is no longer emitted at the call site.
//@ WHY THE PROGRAM IS WRONG: unwrap on None panics.
//@ teeth: FAILED on b98d5d87; verified on the s43 v2 review build.
//@ teeth: the call-site obligation IS emitted (--emit-smt-dir goal `(assert (not (and true (is_some $call_6))))` under `requires y@ == 0`, wp-s48 1229a3db); the
//@ teeth: verdict stays unknown only because ay cannot model-validate SAT under the Option axioms.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(y@ == 0)] #[ensures(true)] pub fn f(x: i64, y: i64) -> i64 { x.checked_div(y).unwrap() }
