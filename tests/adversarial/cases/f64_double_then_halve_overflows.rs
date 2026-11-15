//@ expect: reject
//@ ay-not-unsat: round_trips
//@ mechanism: doubling a finite `f64` above `f64::MAX / 2.0` overflows to infinity, and halving infinity
//@ mechanism: leaves it infinite, so `x * 2.0 / 2.0 == x` fails for every such `x`. Over the reals the
//@ mechanism: product never leaves the line and the round trip is exact. The `x != x` disjunct excuses NaN,
//@ mechanism: so only the overflow refutes the claim.
//@ accept-means: `round_trips(f64::MAX)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: on the campaign tip before D-215 ay answered unsat (exact real arithmetic proves the round
//@ teeth: trip) and only a demotion withheld the credit, so `ay-not-unsat` failed there; rejected after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn round_trips(x: f64) -> bool {
    x != x || x * 2.0 / 2.0 == x
}
