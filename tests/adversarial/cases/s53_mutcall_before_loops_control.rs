//@ expect: verify
//@ xfail: PRE-EXISTING: a pre-loop `&mut` call's postcondition (`^x == -5`) is not turned into a
//@ xfail: binding the later loop's invariant initialization can use, so `x == -5` is unprovable at
//@ xfail: the second loop's entry. Fails identically on the pre-change build (base.out) and after
//@ xfail: this front's fix (c.out): no loop writes x, so no write-site change touches it.
//@ mechanism: control: `setneg(&mut x)` BEFORE the first loop dominates both loops; the later loop's invariant `x == -5` is initialized from the post-call fact
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
pub fn f(n: u32) { let mut x: i32 = 1; setneg(&mut x); let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let mut j: u32 = 0; #[invariant(j <= n && x == -5i32)] while j < n { j += 1; } }
