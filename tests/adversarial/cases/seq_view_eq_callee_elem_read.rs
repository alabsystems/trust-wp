//@ expect: reject
//@ verdict: failed
//@ fn-failed: c_elem
//@ also-verified: same
//@ mechanism: a callee's `result@ == v@` reaches the caller as an equality between two Seq
//@ mechanism: views; the caller's element read on its own result must be answered by the
//@ mechanism: source's element at the SAME index. The result view takes the components of the
//@ mechanism: value it is the view of (view.rs assert_seq_view_identity_components), so a read
//@ mechanism: at index 0 must not see the fact about index 1.
//@ accept-means: the view identity bound components that make distinct indices agree, or the
//@ accept-means: premises became contradictory.
//@ WHY THE CONTRACT IS FALSE: `c_elem(vec![0, 7])` returns `[0, 7]`, whose element 0 is 0, not 7.
//@ teeth: standing shape gate beside the control; not shown to accept on any build.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == v@)]
pub fn same(v: Vec<u32>) -> Vec<u32> { v }

#[requires(v@.len() == 2 && v@[1]@ == 7)]
#[ensures(result@.len() == 2 && result@[0]@ == 7)]
pub fn c_elem(v: Vec<u32>) -> Vec<u32> {
    let r = same(v);
    r
}
