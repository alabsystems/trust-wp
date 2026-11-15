//@ expect: verify
//@ mechanism: control: an exit-tail check provable from the FIRST loop's own invariant (`i <= n`, `n <= 10`) must still verify
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n <= 10u32)]
#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let _y = 10u32 - i; #[invariant(true)] loop { } }
