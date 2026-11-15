//@ expect: verify
//@ mechanism: control for s28_derived_old_suffix_base: a correct `old(*a_id)` contract with no colliding name must still verify (the every-split peel must not over-refuse `a_id` itself).
//@ fixed-by: wp-s28 v9 (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == old(*a_id))]
pub fn g(a_id: &mut u32) -> u32 {
    let r = *a_id;
    *a_id = 5u32;
    r
}
