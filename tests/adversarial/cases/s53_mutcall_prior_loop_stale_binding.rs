//@ expect: reject
//@ mechanism: a `&mut` call argument in a PRIOR loop (`setneg(&mut x)`) was not a write site: the second loop kept the bb0 binding `x == 1`
//@ accept-means: f(1) calls need_pos(-5). FALSE.
//@ fixed-by: wp-s53 loop-write-sites-mut-call-args
//@ teeth: verified (false accept) on the pre-change build of wp-campaign 541d1c75, A/B'd against the post-change build, which rejects
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
pub fn f(n: u32) { let mut x: i32 = 1; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { setneg(&mut x); i += 1; } let mut j: u32 = 0; #[invariant(j <= n)] while j < n { need_pos(x); j += 1; } }
