//@ expect: verify
//@ mechanism: D-96's named price, now paid back: a clause-free body indexes `a[1][i]` over
//@ mechanism: `&[&[u32]]` under `1 < a.len() && i < a[1].len()`. rustc reads the inner check's length
//@ mechanism: through `&raw const (fake) (*a[1])`, which translated to a fresh term, so the guard's
//@ mechanism: `a[1].len()` and the check's length were two terms. D-118 translates the fake pointer
//@ mechanism: as the reference it reads.
//@ accept-means: n/a (control) — both indices are guarded.
//@ fixed-by: n/a (control)
//@ teeth: control — `get verified`; `get FAILED` on the binary before D-118. Its twin
//@ teeth: nested_slice_guard_index_off_by_one is refuted before and after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn get(a: &[&[u32]], i: usize) -> u32 {
    if 1 < a.len() && i < a[1].len() { a[1][i] } else { 0 }
}
