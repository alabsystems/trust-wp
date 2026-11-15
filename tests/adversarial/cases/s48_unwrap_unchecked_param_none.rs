//@ expect: reject
//@ mechanism: requires o.is_none() then unwrap_unchecked (UB).
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ accept-means: the unwrap_unchecked requires is no longer emitted at the call site.
//@ WHY THE PROGRAM IS WRONG: unwrap_unchecked on None is undefined behaviour.
//@ teeth: rejected only as unknown (quantifier-unhandled) on wp-s48, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(o.is_none())]
pub fn f(o: Option<i32>) -> i32 { unsafe { o.unwrap_unchecked() } }
