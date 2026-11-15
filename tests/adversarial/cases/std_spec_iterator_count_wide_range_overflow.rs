//@ expect: reject
//@ verdict: unknown
//@ refused-with: std call can panic under a condition its spec cannot state
//@ mechanism: `Iterator::count` keeps its running count under the caller's overflow checks, and
//@ mechanism: `RangeInclusive::count` panics with "count overflowed usize" when the range holds more
//@ mechanism: than `usize::MAX` values. Its std spec stated no precondition, so every count was
//@ mechanism: trusted. The length of an arbitrary iterator is not a clause a caller can discharge, so
//@ mechanism: the call refuses unless the call site instantiates `Self` with an iterator whose length
//@ mechanism: is a `usize` by construction; a range of `u64` on a 64-bit target is not one.
//@ accept-means: `Iterator::count` is trusted not to overflow again.
//@ fixed-by: D-121 — a panic a std spec cannot state refuses the call, except where the call site
//@ fixed-by: shows it cannot happen.
//@ WHY THE CONTRACT IS FALSE: `f(0..=u64::MAX)` counts `2^64` values, one more than `usize::MAX`,
//@ WHY THE CONTRACT IS FALSE: and panics with "count overflowed usize".
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the `count` requirement reverted; its
//@ teeth: twin std_spec_iterator_count_narrow_range_control differs in the element type alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(r: std::ops::RangeInclusive<u64>) -> usize {
    r.count()
}
