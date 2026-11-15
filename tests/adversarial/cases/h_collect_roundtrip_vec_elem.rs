//@ expect: reject
//@ mechanism: the FALSE twin of h_collect_roundtrip_vec_elem_control: the same round trip, a
//@ mechanism: claim about the element the source does NOT hold. The view of the collected vector
//@ mechanism: shares the source view's components (view.rs assert_seq_view_identity_components),
//@ mechanism: so a sharing that bound the wrong components, or a spec stating more than the view
//@ mechanism: equality, is what would prove it.
//@ accept-means: the element read on the result was answered by something other than the
//@ accept-means: source's element 1.
//@ WHY THE CONTRACT IS FALSE: `c_elem(vec![0, 7])` returns `[0, 7]`, whose element 1 is 7, not 8.
//@ teeth: standing shape gate beside the control; not shown to accept on any build.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 2 && v@[1]@ == 7)]
#[ensures(result@.len() == 2 && result@[1]@ == 8)]
pub fn c_elem(v: Vec<u32>) -> Vec<u32> {
    let r: Vec<u32> = v.into_iter().collect();
    r
}
