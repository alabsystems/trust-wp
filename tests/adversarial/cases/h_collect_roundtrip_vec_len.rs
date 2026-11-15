//@ expect: reject
//@ verdict: failed
//@ mechanism: the FALSE twin of h_collect_roundtrip_vec_len_control. `Vec::into_iter` states
//@ mechanism: Creusot's `self@ == result@` and the gated roundtrip `collect` states
//@ mechanism: `result@ == self@`, so the collected vector has exactly the source's length and
//@ mechanism: no other; a spec that pins a length, or premises that contradict each other, would
//@ mechanism: prove this one too.
//@ accept-means: the into_iter/collect specs stated more than the view equality (or the
//@ accept-means: premises became contradictory).
//@ WHY THE CONTRACT IS FALSE: `c_len(vec![0, 0, 0])` returns a vector of length 3, not 4.
//@ teeth: standing shape gate beside the control; not shown to accept on any build.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 3)]
#[ensures(result@.len() == 4)]
pub fn c_len(v: Vec<u32>) -> Vec<u32> {
    let r: Vec<u32> = v.into_iter().collect();
    r
}
