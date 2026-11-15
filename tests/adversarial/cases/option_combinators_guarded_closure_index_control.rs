//@ expect: verify
//@ mechanism: the isolating control for closure_index_through_option_combinators_uncharged: the SAME
//@ mechanism: combinators, each closure guarding its index by the slice's length. Each closure
//@ mechanism: reads the captured slice's length for the guard and for the bounds check through one
//@ mechanism: term (the bounds check's `&raw const (fake)` pointer is translated as the reference
//@ mechanism: the guard reads), and verifies under `requires true`. `bool::then` is left out: its
//@ mechanism: guarded host is `unknown` before and after D-118 on a fail-closed `false` trust-wp
//@ mechanism: injects for a construct it cannot model, so it cannot be a control today.
//@ accept-means: n/a (control) — no index leaves its slice.
//@ fixed-by: n/a (control)
//@ teeth: control — every host and every closure verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 1)]
pub fn via_and_then(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.and_then(|j| if j < w.len() { Some(w[j]) } else { None });
    1
}

#[ensures(result@ == 1)]
pub fn via_unwrap_or_else(o: Option<u32>, w: &[u32], k: usize) -> u32 {
    let _ = o.unwrap_or_else(|| if k < w.len() { w[k] } else { 0 });
    1
}

#[ensures(result@ == 1)]
pub fn via_result_map(o: Result<usize, u32>, w: &[u32]) -> u32 {
    let _ = o.map(|j| if j < w.len() { w[j] } else { 0 });
    1
}
