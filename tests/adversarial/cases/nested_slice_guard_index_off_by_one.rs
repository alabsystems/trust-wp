//@ expect: reject
//@ verdict: failed
//@ fn-failed: get
//@ mechanism: the RED twin of nested_slice_guard_index_control: `i <= a[1].len()`, so
//@ mechanism: `get(&[&[], &[]], 0)` indexes past the end of `a[1]`. A fake-pointer translation that
//@ mechanism: read a length other than `a[1]`'s would verify this.
//@ accept-means: `get(&[&[], &[]], 0)` panics with "index out of bounds" and is credited.
//@ WHY IT IS FALSE: `a[1]` is empty and `i == 0` passes `i <= a[1].len()`.
//@ fixed-by: D-118
//@ teeth: refuted before and after D-118.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn get(a: &[&[u32]], i: usize) -> u32 {
    if 1 < a.len() && i <= a[1].len() { a[1][i] } else { 0 }
}
