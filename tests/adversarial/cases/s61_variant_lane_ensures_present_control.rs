//@ expect: reject
//@ mechanism: lane-choice control for s61_variant_lane_pa_false — the SAME false assertion, with `#[ensures]` added. `verify_recursive_variant_decrease` then returns false (recursive_verify.rs:992 tests `ensures.is_empty()`), the function-level lane runs, and the crate is rejected on the campaign build too.
//@ accept-means: the lane that skipped the assertion was reached even with `ensures` present.
//@ fixed-by: n/a — this case must be rejected before AND after wp-s61; it pins that the LANE CHOICE, not the assertion, decided the sibling case.
//@ teeth: n/a by construction — rejected on wp-campaign 04fc8074 as well (exit 2, `countdown3 unknown (proof-trusted)`); its value is that its sibling was ACCEPTED on the same build.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[variant(n)]
#[ensures(result == 0u32)]
pub fn countdown3(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        proof_assert!(false);
        countdown3(n - 1)
    }
}
