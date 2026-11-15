//@ expect: reject
//@ mechanism: sequential loops: a stale pre-loop binding of the first loop's counter at the second loop's header would discharge a call precondition about it
//@ accept-means: f(0) calls need_pos(-1). FALSE.
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
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let mut j: u32 = 0; #[invariant(j <= n)] while j < n { need_pos((i as i32) - 1); j += 1; } }
