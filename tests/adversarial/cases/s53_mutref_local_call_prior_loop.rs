//@ expect: reject
//@ mechanism: a `&mut` held in a local (`let r = &mut x`, made before the loops) and passed to `setneg(r)` in a prior loop was not a write site of x
//@ accept-means: f(1) calls need_pos(-5). FALSE.
//@ fixed-by: wp-s53 loop-write-sites-mut-call-args
//@ teeth: verified (false accept) on the pre-change build of wp-campaign 541d1c75 (same-session A/B against the post-change build, which rejects it)
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
pub fn f(n: u32) { let mut x: i32 = 1; let r = &mut x; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { setneg(r); i += 1; } let mut j: u32 = 0; #[invariant(j <= n)] while j < n { need_pos(x); j += 1; } }
