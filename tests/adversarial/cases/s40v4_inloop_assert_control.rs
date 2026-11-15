//@ expect: verify
//@ mechanism: control: an in-loop assert! panic arm stays checked under the established loop condition
//@ accept-means: n/a (control) — `i < n` holds inside the loop; TRUE contract
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { assert!(i < n); i += 1; } }
