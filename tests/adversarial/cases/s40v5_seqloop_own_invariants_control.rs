//@ expect: verify
//@ mechanism: control: sequential loops each proving their own invariant must still verify under per-loop invariant scoping
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } let mut j: u32 = 0; #[invariant(j <= n)] while j < n { j += 1; } }
