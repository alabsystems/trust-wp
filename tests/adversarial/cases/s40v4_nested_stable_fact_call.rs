//@ expect: reject
//@ mechanism: nested loops: the inner loop's stale pre-loop binding `j = 0` became the stable invariant `j == 0` and discharged an inner-loop call precondition
//@ accept-means: f(2) calls need0(1). FALSE.
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: verified (false accept) on 5becf6c8, the merged wp-campaign + v3 pre-change build (A/B 2026-09-13)
//@ also-verified: need0
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(j@ == 0)]
pub fn need0(j: u32) {}
#[ensures(true)]
pub fn f(n: u32) { let mut j: u32 = 0; #[invariant(j <= n)] while j < n { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { need0(j); i += 1; } j += 1; } }
