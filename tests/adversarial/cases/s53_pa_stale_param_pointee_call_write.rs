//@ expect: reject
//@ mechanism: the loop writes the parameter's pointee through a CALL (`set(a)`), which the write-site walk follows to the parameter
//@ accept-means: `*a` is 7 after the loop, and `(*a)@ == 0` is discharged by the stale entry fact. FALSE.
//@ fixed-by: wp-s53 loop-invalidated parameter facts
//@ teeth: verified ✓ (exit 0) on wp-campaign ff8f5aa6, with proof_assert_verified=0 — the assertion was never examined (A/B'd against the post-change build)
//@ also-verified: set, f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures((^x)@ == 7)]
pub fn set(x: &mut u32) { *x = 7; }

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32, n: u32) { let mut i = 0u32; #[invariant(i@ <= n@)] while i < n { set(a); i += 1; } proof_assert!((*a)@ == 0); }
