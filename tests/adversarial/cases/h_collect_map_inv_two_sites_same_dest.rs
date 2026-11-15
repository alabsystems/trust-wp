//@ expect: reject
//@ mechanism: map_inv collect view facts — two collect call sites writing the same local must each get their own symbol
//@ fixed-by: wp-s24 (collect-hardening-v2)
//@ accept-means: the first collect's length fact (3) was applied to the overwritten value. Refuting execution: v is reassigned from (0..5), so result@.len() == 5, not 3.
//@ teeth: UNVERIFIED as a defect detector — on wp-s24 it ends FAILED (postcondition).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// FALSE: v is overwritten by the second collect (len 5), claim len 3.
#[ensures(result@.len() == 3)]
pub fn twice() -> Vec<u32> {
    let mut v: Vec<u32> = (0u32..3).map_inv(|x, _| x).collect();
    v = (0u32..5).map_inv(|x, _| x).collect();
    v
}
