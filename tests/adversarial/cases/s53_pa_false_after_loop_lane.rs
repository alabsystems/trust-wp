//@ expect: reject
//@ mechanism: the loop lane returned `Handled` and the caller returned before verifying ANY in-function proof_assert
//@ accept-means: `proof_assert!(false)` is credited without ever being examined. FALSE.
//@ fixed-by: wp-s53 loop-lane in-function assertions
//@ teeth: verified ✓ (exit 0) on wp-campaign ff8f5aa6, with proof_assert_verified=0 — the assertion was never examined; A/B'd against the post-change build
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() { let mut i = 0u32; #[invariant(i@ <= 3)] while i < 3 { i += 1; } proof_assert!(false); }
