//@ expect: reject
//@ mechanism: same loop-lane `Handled` return: the assertion over a local the loop overwrites was never examined
//@ accept-means: x is 7 after the loop, and `x@ == 0` is credited. FALSE.
//@ fixed-by: wp-s53 loop-lane in-function assertions
//@ teeth: verified ✓ (exit 0) on wp-campaign ff8f5aa6, with proof_assert_verified=0 — the assertion was never examined (measured as an A/B against the fixed build)
//@ also-verified: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() { let mut x = 0u32; let mut i = 0u32; #[invariant(i@ <= 3)] while i < 3 { x = 7; i += 1; } proof_assert!(x@ == 0); }
