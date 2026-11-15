//@ expect: reject
//@ mechanism: the recursive-`#[variant]` lane owned the verdict by RETURNING from verify_single_contract (per_contract.rs:313), before the in-function proof_assert pass — and the standalone fallback pass skips any function carrying a `variants` clause, so NO lane examined the assertion
//@ accept-means: `proof_assert!(false)` inside a recursive `#[variant]` function is credited without ever being examined. FALSE — `countdown(1)` reaches it.
//@ fixed-by: wp-s61 one shared tail for every lane of verify_single_contract
//@ teeth: ACCEPTED, exit 0, `trust-wp: countdown verified ✓ (termination)` with `1 verified, 0 failed, 0 errors` and proof_assert_verified=0, on wp-campaign 04fc8074 (A/B 2026-09-14, <session-scratch>/ab.log)
//@ also-verified: countdown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[variant(n)]
pub fn countdown(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        proof_assert!(false);
        countdown(n - 1)
    }
}
