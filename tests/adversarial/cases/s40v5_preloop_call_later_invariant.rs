//@ expect: reject
//@ mechanism: the pre-loop call-obligation lane assumed every loop's effective invariants; a loop invariant established after the call (`x = 5`) must not discharge the call's precondition
//@ accept-means: f(-1) calls need_pos(-1). FALSE.
//@ fixed-by: wp-s40 loop-invariant-pooling-v5
//@ also-verified: need_pos
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x > 0i32)]
pub fn need_pos(x: i32) {}
#[ensures(true)]
pub fn f(y: i32) { let mut x: i32 = y; need_pos(x); x = 5; #[invariant(x > 0i32)] loop { } }
