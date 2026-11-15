//@ expect: reject
//@ mechanism: Rust's float `%` truncates the quotient toward zero, so the remainder takes the dividend's
//@ mechanism: sign: `-7.0 % 5.0` is `-2.0`, not the floored (Euclidean) `3.0`. D-215 folds an operator over
//@ mechanism: two literals on the host by Rust's own `%`; a fold by another convention (`rem_euclid`, a
//@ mechanism: real-number `mod`) would accept. f64_literal_rem_truncates_control.rs is the same body under
//@ mechanism: the true claim.
//@ accept-means: `rem_floored()` and `rem_floored_f32()` return `false`; an accept claims they return `true`.
//@ fixed-by: D-215
//@ teeth: FAILED (`rem_floored`, `rem_floored_f32`) on the campaign tip before D-215, while D-215 left `%`
//@ teeth: untranslated, and with `%` folded on the host by Rust's own remainder: it pins the fold against
//@ teeth: another convention and caught no live defect.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn rem_floored() -> bool {
    -7.0f64 % 5.0 == 3.0
}

#[ensures(result)]
pub fn rem_floored_f32() -> bool {
    -7.5f32 % 2.0f32 == 0.5f32
}
