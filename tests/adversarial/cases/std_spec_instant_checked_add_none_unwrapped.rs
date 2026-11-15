//@ expect: reject
//@ verdict: unknown
//@ mechanism: `Instant::checked_add`'s std spec claimed `None => false`: the abstract `Int` view
//@ mechanism: has no upper bound, so the add was taken never to fail, and an `unwrap` of it was
//@ mechanism: discharged. The platform clock does have a bound. The spec now admits `None` for every
//@ mechanism: positive duration.
//@ accept-means: `checked_add` is again claimed never to return `None`.
//@ fixed-by: D-121 — a std spec claims no more than its function guarantees.
//@ WHY THE CONTRACT IS FALSE: adding `u64::MAX` seconds to any instant leaves the clock's range,
//@ WHY THE CONTRACT IS FALSE: `checked_add` returns `None`, and the `unwrap` panics.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_instant_checked_add_zero_control adds zero instead and verifies.
//@ teeth: The `unwrap`'s precondition is left unproved, `f unknown (quantifier-unhandled)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::{Duration, Instant};

#[ensures(true)]
pub fn f() -> bool {
    let t = Instant::now().checked_add(Duration::from_secs(u64::MAX)).unwrap();
    t == t
}
