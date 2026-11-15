//@ expect: reject
//@ mechanism: the RED twin of double_ref_slice_guard_index_control: `j <= w.len()`, so
//@ mechanism: `hop(0, &&[][..])` indexes past the end. The fake pointer is translated as the
//@ mechanism: reference it reads; a translation that fabricated a larger length would verify this.
//@ accept-means: `hop(0, &&[][..])` panics with "index out of bounds" and the crate is credited.
//@ fixed-by: D-118
//@ teeth: refuted before and after D-118.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn hop(j: usize, w: &&[u32]) -> u32 {
    if j <= w.len() { w[j] } else { 0 }
}
