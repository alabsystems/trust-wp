//@ expect: verify
//@ mechanism: control: a later loop reads a variable no loop writes while a prior loop runs `setneg(&mut x)` on another variable
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
pub fn f(n: u32) { let mut x: i32 = 1; let y: i32 = 3; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { setneg(&mut x); i += 1; } let mut j: u32 = 0; #[invariant(j <= n)] while j < n { need_pos(y); j += 1; } }
