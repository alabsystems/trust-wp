//@ expect: reject
//@ mechanism: a later loop indexed `a[x]` with x resolved to the stale bb0 binding `0` across a prior loop that runs `setbig(&mut x)`
//@ accept-means: f(1) indexes a 3-element array at 5. FALSE.
//@ fixed-by: wp-s53 loop-write-sites-mut-call-args
//@ teeth: verified (false accept) on the pre-change build of wp-campaign 541d1c75 (A/B against the post-change build, which refuses it)
//@ also-verified: need_pos, setbig
//@
//@ The `10i32 / (x - (-5i32))` shape of the same defect (adv5 q12) was NOT a
//@ case here when this front was written: no lane emitted an obligation for a
//@ MIR `DivisionByZero` assert, in or out of a loop, so that accept survived
//@ this fix. wp-campaign e3dae772 (s16 v4) added the obligation, and q12 is
//@ refused on this branch — by BOTH halves: the divisor obligation exists, and
//@ this front stops x resolving to its stale bb0 value inside the later loop.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x > 0i32)]
pub fn need_pos(x: i32) {}

#[ensures(^x == 5usize)]
pub fn setbig(x: &mut usize) { *x = 5; }

#[ensures(true)]
pub fn f(n: u32) { let a = [1i32, 2i32, 3i32]; let mut x: usize = 0; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { setbig(&mut x); i += 1; } let mut j: u32 = 0; #[invariant(j <= n)] while j < n { let _z = a[x]; j += 1; } }
