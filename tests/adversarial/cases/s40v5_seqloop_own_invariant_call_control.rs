//@ expect: verify
//@ mechanism: control: a call in the second loop discharged by the SECOND loop's own invariant (`x == 5`) must still verify
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x > 0i32)]
pub fn need_pos(x: i32) {}
#[ensures(true)]
pub fn f(y: i32, n: u32) { let mut x: i32 = y; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } x = 5; let mut j: u32 = 0; #[invariant(x == 5i32 && j <= n)] while j < n { need_pos(x); j += 1; } }
