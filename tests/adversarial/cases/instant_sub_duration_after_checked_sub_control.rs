//@ expect: verify
//@ mechanism: the over-refusal half of the `Instant - Duration` pair. The operator is
//@ mechanism: `checked_sub(rhs).expect(..)`, so it owes what makes `checked_sub` return `Some`: the
//@ mechanism: `Some` arm of `Instant::checked_sub`'s own spec, `self@ >= rhs@`. `guarded` subtracts
//@ mechanism: only where `checked_sub` answered `Some`, so the bound is discharged by the spec that
//@ mechanism: grants it; `within_bound` has it from its own `requires`.
//@ accept-means: n/a (control) — both contracts are TRUE: `guarded` returns `true`, and
//@ accept-means: `within_bound` subtracts only a duration no longer than the instant's view.
//@ fixed-by: D-137
//@ teeth: both verified before D-121 (no requirement at all), refused under D-121's
//@ teeth: `unmodelled_panic` marker, verified under D-137. The false twin is
//@ teeth: instant_duration_operators_param_unbounded_panics (`sub_any`, the same subtraction with
//@ teeth: no bound), and instant_sub_underflow_panic_uncharged for a literal operand.
//@ note: `match i.checked_sub(d) { Some(j) => i - d == j, .. }` states the same fact and is
//@ note: `unknown (timeout)`: the `Some` arm of an `Option<Instant>` match is the arm D-116 found
//@ note: ay cannot certify; the `is_some()` guard reaches the same precondition without it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn guarded() -> bool {
    let i = Instant::now();
    let d = Duration::from_secs(3);
    if i.checked_sub(d).is_some() {
        let _k = i - d;
    }
    true
}

#[requires(i@ >= d@)]
#[ensures(result@ == i@ - d@)]
pub fn within_bound(i: Instant, d: Duration) -> Instant {
    i - d
}
