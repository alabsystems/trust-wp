//@ expect: verify
//@ mechanism: a contract-free extern -> ! call made unreachable by the caller precondition
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

unsafe extern "C" { fn abort() -> !; }
#[requires(x@ > 0)]
#[ensures(true)]
pub fn f(x: i32) { if x <= 0 { unsafe { abort() } } }
