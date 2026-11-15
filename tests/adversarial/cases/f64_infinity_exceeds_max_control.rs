//@ expect: verify
//@ mechanism: infinity is a float value above every finite one: `f64::INFINITY > f64::MAX` holds in IEEE-754
//@ mechanism: and must be decided by a float model that has infinities as values.
//@ accept-means: n/a (control) — the comparison is `true` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: verified beside the float RED cases.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn infinity_exceeds_max() -> bool {
    let inf = f64::INFINITY;
    let max = f64::MAX;
    inf > max
}
