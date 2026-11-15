//@ expect: reject
//@ mechanism: the sibling of instant_add_overflow_panic_uncharged.rs for `Instant - Duration`. The
//@ mechanism: builtin spec (the combined `Sub` spec, which also serves `Instant - Instant`) states no
//@ mechanism: precondition, and where `self@ < rhs@` it gives `result@ == 0` although the call
//@ mechanism: panics there ("overflow when subtracting duration from instant"). `j <= i` follows
//@ mechanism: from the spec on both arms.
//@ accept-means: a std spec that omits a panic precondition lets a contract-bearing body that
//@ accept-means: panics on every call verify.
//@ accept-means: `sub_huge_not_later()` panics on every call: `Instant::now() -
//@ accept-means: Duration::from_secs(u64::MAX)` underflows the timestamp's i64 seconds
//@ accept-means: (run with stock rustc on aarch64-apple-darwin).
//@ fixed-by: D-137 — the call site tells the two impls apart (`__trust_wp_std_site_same_Self_Rhs()`,
//@ fixed-by: `false` here), and `Instant - Duration` owes `self@ >= rhs@`, the `Some` arm of
//@ fixed-by: `checked_sub`'s spec; `Instant - Instant` owes nothing (std_spec_instant_sub_instant_control).
//@ teeth: ACCEPTED (`sub_huge_not_later verified`, exit 0) when committed; `unknown` on D-121's
//@ teeth: refused marker; FAILED on `self@ >= rhs@` under D-137.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn sub_huge_not_later() -> bool {
    let i = Instant::now();
    let j = i - Duration::from_secs(u64::MAX);
    j <= i
}
