//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: `[T]::rotate_right(k)` (and `rotate_left(mid)`) panics when the count exceeds the
//@ mechanism: length, and its std spec stated only that the length is kept. It now owes
//@ mechanism: `k@ <= self@.len()`.
//@ accept-means: the slice rotation specs stopped owing their out-of-range panic.
//@ fixed-by: D-121 — a std spec owes every panic of its function it can state.
//@ WHY THE CONTRACT IS FALSE: `f` admits the empty slice, and rotating it right by one panics.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_slice_rotate_right_in_range_control differs in the `requires`
//@ teeth: alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(s: &mut [u32]) {
    s.rotate_right(1);
}
