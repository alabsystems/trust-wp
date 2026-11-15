//@ expect: reject
//@ mechanism: the same early return also dropped the function-level VC, which is NOT empty when `ensures` is: `contract_transform` merges the call-site precondition obligations (call_obligation_ensures) into it. A recursive `#[variant]` function with no `#[ensures]` could violate any callee's `requires` unexamined.
//@ accept-means: `needs_positive(n - 1)` is credited at n == 1, where its `#[requires(x > 0)]` is violated. FALSE — `countdown2(1)` calls `needs_positive(0)`.
//@ fixed-by: wp-s61 — the termination lane may own the verdict only when parsed.call_obligations is empty and extraction did not fail closed
//@ teeth: ACCEPTED, exit 0, `2 verified, 0 failed, 0 errors` on wp-campaign 04fc8074 (A/B 2026-09-14, <session-scratch>/ab.log)
//@ also-verified: needs_positive
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x > 0u32)]
pub fn needs_positive(x: u32) -> u32 {
    x
}

#[variant(n)]
pub fn countdown2(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        let _ = needs_positive(n - 1);
        countdown2(n - 1)
    }
}
