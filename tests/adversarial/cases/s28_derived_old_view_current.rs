//@ expect: reject
//@ mechanism: `old(*view)` is Var("old_view_current"); the first-match peel took old_view_current -> old_view -> old and never reached the base `view`.
//@ fixed-by: wp-s28 v9 (derived_name_bases explores every split)
//@ accept-means: g proved its result equals the pre-state of *view while returning an unrelated parameter.
//@ teeth: exit-0 false accept (`g verified ✓`) on 8c8fa32f and on merged 279f88a0 (review-probes/rv9-before/d2).
//@ verdict: error
//@ refused-with: `old_view_current` is spelled as a name the verifier derives from `view`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == old(*view))]
pub fn g(view: &mut u32, old_view_current: u32) -> u32 {
    *view = 1u32;
    old_view_current
}
