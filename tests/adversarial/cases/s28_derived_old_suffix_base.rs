//@ expect: reject
//@ mechanism: the encoder names `old(*a_id)` Var("old_a_id_current"); derived_name_bases peeled only the first match per layer (old_a_id, old_a, a) and never reached the base `a_id`, so the parameter `old_a_id_current` was the same solver constant.
//@ fixed-by: wp-s28 v9 (derived_name_bases explores every prefix/suffix/_ssa_ split)
//@ accept-means: g proved its result equals the pre-state of *a_id while returning an unrelated parameter.
//@ teeth: exit-0 false accept (`g verified ✓`) on 8c8fa32f and on merged 279f88a0 (review-probes/rv9-before/d1); renamed control s28_derived_old_suffix_base_renamed is unknown, not refused.
//@ verdict: error
//@ refused-with: `old_a_id_current` is spelled as a name the verifier derives from `a_id`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == old(*a_id))]
pub fn g(a_id: &mut u32, old_a_id_current: u32) -> u32 {
    *a_id = 5u32;
    old_a_id_current
}
