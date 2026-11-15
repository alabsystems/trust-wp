//@ expect: verify
//@ mechanism: the control for f64_literal_rem_read_as_floored.rs, the same bodies under the true claims:
//@ mechanism: Rust's `%` gives `-7.0 % 5.0 == -2.0` and `-7.5f32 % 2.0f32 == -1.5f32`.
//@ accept-means: n/a (control) — `rem_truncated()` and `rem_truncated_f32()` return `true` in every execution.
//@ fixed-by: n/a (control)
//@ teeth: failed on the campaign tip before D-215 and while D-215 left `%` untranslated; verified with `%`
//@ teeth: folded on the host by Rust's own remainder.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn rem_truncated() -> bool {
    -7.0f64 % 5.0 == -2.0
}

#[ensures(result)]
pub fn rem_truncated_f32() -> bool {
    -7.5f32 % 2.0f32 == -1.5f32
}
