//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_iterator_count_wide_range_overflow, identical but for the
//@ mechanism: element type: an inclusive range of `u32` holds at most `2^32` values, which a
//@ mechanism: 64-bit `usize` counts. It pins the over-refusal side: a `count` spec that refuses
//@ mechanism: every call is no fix.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(r: std::ops::RangeInclusive<u32>) -> usize {
    r.count()
}
