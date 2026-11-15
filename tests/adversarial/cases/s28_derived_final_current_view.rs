//@ expect: reject
//@ mechanism: `(^current)@` is Var("final_current_view"); the first-match peel took final_current_view -> final_current -> final and never reached the base `current`.
//@ fixed-by: wp-s28 v9 (derived_name_bases explores every split)
//@ accept-means: g proved the final view of `current` equals an unrelated parameter.
//@ teeth: unknown (not refused) on 279f88a0 (review-probes/rv9-before/d5).
//@ verdict: error
//@ refused-with: `final_current_view` is spelled as a name the verifier derives from `current`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((^current)@ == final_current_view@)]
pub fn g(current: &mut Vec<u32>, final_current_view: Vec<u32>) {}
