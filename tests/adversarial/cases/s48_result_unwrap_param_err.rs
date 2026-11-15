//@ expect: reject
//@ mechanism: requires r.is_err() then r.unwrap().
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ accept-means: the Result::unwrap requires is no longer emitted at the call site.
//@ WHY THE PROGRAM IS WRONG: unwrap on Err panics.
//@ teeth: rejected only as unknown (quantifier-unhandled) on wp-s48, measured 2026-09-13.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(r.is_err())]
pub fn f(r: Result<i32, u8>) -> i32 { r.unwrap() }
