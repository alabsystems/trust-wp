//@ expect: reject
//@ mechanism: the builtin std spec of `Instant + Duration` is `result@ == self@ + rhs@` with no
//@ mechanism: precondition, read over an unbounded Int view. The view is unbounded; the platform
//@ mechanism: clock is not, and `Add::add` panics ("overflow when adding duration to instant")
//@ mechanism: where `checked_add` would return `None`. D-116 withdrew the never-`None` claim from
//@ mechanism: `checked_add`; the operator spelling still claims the call always returns. With the
//@ mechanism: duration's view known positive (`from_secs(u64::MAX)`), `j > i` follows from the spec.
//@ accept-means: a std spec that omits a panic precondition lets a contract-bearing body that
//@ accept-means: panics on every call verify.
//@ accept-means: `add_huge_is_later()` panics on every call: `Instant::now() +
//@ accept-means: Duration::from_secs(u64::MAX)` overflows the timestamp's i64 seconds
//@ accept-means: (run with stock rustc on aarch64-apple-darwin).
//@ fixed-by: D-137 — the operator is `checked_add(..).expect(..)` and owes what makes
//@ fixed-by: `checked_add` return `Some`; its spec promises that for a zero duration only, so the
//@ fixed-by: operator owes `rhs@ == 0`. Creusot's spec for this operator owes nothing and accepts.
//@ teeth: ACCEPTED (`add_huge_is_later verified`, exit 0) when committed; `unknown` on D-121's
//@ teeth: refused marker, which also refused instant_add_zero_duration_control; FAILED on
//@ teeth: `rhs@ == 0` under D-137, with that control verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn add_huge_is_later() -> bool {
    let i = Instant::now();
    let j = i + Duration::from_secs(u64::MAX);
    j > i
}
