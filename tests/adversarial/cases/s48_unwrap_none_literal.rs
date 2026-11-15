//@ expect: reject
//@ mechanism: Option::unwrap precondition `*self != None` on a literal None.
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ accept-means: the unwrap requires is no longer emitted at the call site.
//@ WHY THE PROGRAM IS WRONG: unwrap on None panics.
//@ teeth: rejected only as unknown (quantifier-unhandled) on b98d5d87; the s43 v2 review saw this family verify on an earlier build.
//@ teeth: the call-site obligation IS emitted (--emit-smt-dir goal `(assert (not (and true (is_some logic_None))))`, wp-s48 1229a3db); the
//@ teeth: verdict stays unknown only because ay cannot model-validate SAT under the Option axioms.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)] pub fn f() -> i32 { let o: Option<i32> = None; o.unwrap() }
