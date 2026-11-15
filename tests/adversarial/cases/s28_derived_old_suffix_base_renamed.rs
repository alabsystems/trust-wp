//@ expect: reject
//@ mechanism: control for s28_derived_old_suffix_base: same wrong contract with the second parameter renamed to `q`, so no name collides; it must be rejected WITHOUT the derived-name refusal.
//@ fixed-by: wp-s28 v9 (control)
//@ accept-means: the wrong contract is proved without any name collision (an unrelated soundness defect).
//@ teeth: unknown (incomplete), exit 2, on 279f88a0 and after the fix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == old(*a_id))]
pub fn g(a_id: &mut u32, q: u32) -> u32 {
    *a_id = 5u32;
    q
}
