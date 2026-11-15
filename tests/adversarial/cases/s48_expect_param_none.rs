//@ expect: reject
//@ mechanism: requires o.is_none() then o.expect(..).
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ accept-means: the expect requires is no longer emitted at the call site.
//@ WHY THE PROGRAM IS WRONG: expect on None panics.
//@ teeth: rejected only as unknown (quantifier-unhandled) on wp-s48, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(o.is_none())]
pub fn f(o: Option<i32>) -> i32 { o.expect("x") }
