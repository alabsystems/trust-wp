//@ expect: reject
//@ mechanism: over integers `!(x < y)` is `x >= y`, and a rewrite that turns one into the other is
//@ mechanism: sound. Over IEEE-754 floats it is not: every ordered comparison with NaN is false, so
//@ mechanism: `!(NaN < y)` is true while `NaN >= y` is false. D-215 sends each float comparison to
//@ mechanism: the solver as a reserved IEEE call that no integer rewrite sees into; the reals have no NaN
//@ mechanism: and prove the equivalence. i64_not_lt_read_as_ge_control.rs is the same body over `i64`.
//@ accept-means: `lt_complement_is_ge(f64::NAN, 0.0)` returns `false`; an accept claims it returns `true`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED on the campaign tip before D-215 (`lt_complement_is_ge verified`,
//@ teeth: `le_complement_is_gt verified`: the reals prove each equivalence); both FAILED after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn lt_complement_is_ge(x: f64, y: f64) -> bool {
    !(x < y) == (x >= y)
}

#[ensures(result)]
pub fn le_complement_is_gt(x: f64, y: f64) -> bool {
    !(x <= y) == (x > y)
}
