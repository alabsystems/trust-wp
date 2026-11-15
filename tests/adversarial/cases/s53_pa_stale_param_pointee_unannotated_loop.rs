//@ expect: reject
//@ mechanism: the same stale entry fact, with an UNANNOTATED loop (the function-level lane, not the loop lane)
//@ accept-means: `*a` is 7 after the loop, and `(*a)@ == 0` is discharged by the stale entry fact. FALSE.
//@ fixed-by: wp-s53 loop-invalidated parameter facts
//@ teeth: verified ✓ (exit 0) on wp-campaign ff8f5aa6, and proof_assert_verified=1 — the assertion was DISCHARGED by the stale entry fact (A/B against the post-fix build)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) { let mut i = 0u32; while i < 3 { *a = 7; i += 1; } proof_assert!((*a)@ == 0); }
