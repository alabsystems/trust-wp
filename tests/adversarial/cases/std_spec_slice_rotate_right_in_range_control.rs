//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_slice_rotate_right_past_len_panics, identical but for the
//@ mechanism: `requires` that rules the empty slice out.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(s@.len() >= 1)]
#[ensures(true)]
pub fn f(s: &mut [u32]) {
    s.rotate_right(1);
}
