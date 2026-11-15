//@ expect: reject
//@ mechanism: the `#[requires]` fact about the ENTRY pointee survived a loop that writes `*a`; the encoder names both values `a_current`
//@ accept-means: `*a` is 7 after the loop, and `(*a)@ == 0` is discharged by the stale entry fact. FALSE.
//@ fixed-by: wp-s53 loop-invalidated parameter facts
//@ teeth: verified ✓ (exit 0) on wp-campaign ff8f5aa6, with proof_assert_verified=0 — the assertion was never examined (A/B'd against the changed build)
//@ also-verified: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) { let mut i = 0u32; #[invariant(i@ <= 3)] while i < 3 { *a = 7; i += 1; } proof_assert!((*a)@ == 0); }
