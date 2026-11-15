//@ expect: reject
//@ mechanism: control for s28_synth_reborrow_child_param with the second parameter renamed; the contract is still FALSE (q is never written).
//@ fixed-by: wp-s28 v8
//@ accept-means: g proved it wrote 7 through q.
//@ teeth: unknown on 42eabec9 (review-probes/sound1/p_rbn).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: q is never written
#[ensures(^q == 7u32)]
pub fn g(x: &mut u32, q: &mut u32) { let y = &mut *x; *y = 7u32; }
