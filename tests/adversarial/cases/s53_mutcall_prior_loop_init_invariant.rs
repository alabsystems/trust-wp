//@ expect: reject
//@ mechanism: a later loop's initialization `x == 1` was proven from the stale bb0 binding across a prior loop that runs `setneg(&mut x)`
//@ accept-means: the invariant `x == 1i32` is false at the second loop entry when n > 0. FALSE.
//@ fixed-by: wp-s53 loop-write-sites-mut-call-args
//@ teeth: verified (false accept) on the pre-change build of wp-campaign 541d1c75, A/B'd in one workspace against the changed build
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
pub fn f(n: u32) { let mut x: i32 = 1; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { setneg(&mut x); i += 1; } let mut j: u32 = 0; #[invariant(j <= n && x == 1i32)] while j < n { j += 1; } }
