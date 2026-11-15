//@ expect: verify
//@ mechanism: control for the bounds-check pointer translation of D-118: indexing through `&&[u32]`
//@ mechanism: under `j < w.len()`. rustc reads the check's length through `&raw const (fake)
//@ mechanism: (*(*w))`, which translated to nothing (a fresh `$_N`), so the guard's `w@.len()` and
//@ mechanism: the check's length were two terms and the guarded index was refuted. A closure indexing
//@ mechanism: a captured slice reads it the same way.
//@ accept-means: n/a (control) — the index is guarded.
//@ fixed-by: n/a (control)
//@ teeth: control — `hop verified`; refuted on the binary before D-118. Its twin
//@ teeth: double_ref_slice_guard_index_off_by_one is refuted.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn hop(j: usize, w: &&[u32]) -> u32 {
    if j < w.len() { w[j] } else { 0 }
}
