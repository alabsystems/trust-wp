//@ expect: reject
//@ mechanism: the builtin std spec of `Duration + Duration` is `result@ == self@ + rhs@` with no
//@ mechanism: precondition, so a sum past `Duration::MAX` is assumed to return. `Add::add` panics
//@ mechanism: there ("overflow when adding durations"). Creusot's spec states the bound as a
//@ mechanism: precondition, `self@ + rhs@ <= secs_to_nanos(u64::MAX@) + 999_999_999`, which this
//@ mechanism: body cannot discharge; trust-wp is weaker than the oracle here.
//@ accept-means: a std spec that omits a panic precondition lets a contract-bearing body that
//@ accept-means: panics on every call verify.
//@ accept-means: `dur_add_huge()` panics on every call: `u64::MAX` seconds plus one
//@ accept-means: second overflows the seconds counter (run with stock rustc).
//@ fixed-by: D-121 — the spec owes Creusot's precondition, `self@ + rhs@ <= u64::MAX@ *
//@ fixed-by: 1_000_000_000 + 999_999_999`; duration_add_small_sum_control.rs still verifies.
//@ teeth: ACCEPTED (`dur_add_huge verified`, exit 0) when committed; FAILED on the precondition
//@ teeth: under D-121.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::Duration;

#[ensures(result)]
pub fn dur_add_huge() -> bool {
    let a = Duration::from_secs(u64::MAX);
    let d = a + Duration::from_secs(1);
    d > a
}
