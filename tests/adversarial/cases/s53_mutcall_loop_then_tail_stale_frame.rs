//@ expect: reject
//@ mechanism: a `&mut` call argument in a loop body was absent from the loop's changed-places set: x kept its pre-loop value `1` after the loop
//@ accept-means: f(1) calls need_pos(-5) after the loop. FALSE.
//@ fixed-by: wp-s53 loop-write-sites-mut-call-args
//@ teeth: verified (false accept) on the pre-change build of wp-campaign 541d1c75, measured as an A/B of that build against the fixed one
//@ also-verified: need_pos, setneg
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x > 0i32)]
pub fn need_pos(x: i32) {}

#[ensures(^x == -5i32)]
pub fn setneg(x: &mut i32) { *x = -5; }

#[ensures(true)]
pub fn f(n: u32) { let mut x: i32 = 1; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { setneg(&mut x); i += 1; } need_pos(x); #[invariant(true)] loop { } }
