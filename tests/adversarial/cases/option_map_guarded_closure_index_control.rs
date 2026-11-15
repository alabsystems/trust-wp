//@ expect: verify
//@ mechanism: the isolating control for closure_index_through_option_map_uncharged: the SAME
//@ mechanism: contracted host, the SAME `Option::map`, the SAME closure indexing the SAME slice by
//@ mechanism: the SAME value, with the index guarded by `j < w.len()` inside the closure. Creusot
//@ mechanism: proves it: the closure's precondition (its body's weakest precondition) is `true`.
//@ mechanism: A fix that charges the closure's bounds check at the combinator call, or makes the
//@ mechanism: closure a target, must keep this verifying.
//@ accept-means: n/a (control) — this contract is TRUE and the body cannot panic.
//@ fixed-by: n/a (control)
//@ teeth: control — verifies. Its RED twin differs only in the guard.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

#[requires(k@ < 10)]
#[ensures(result@ == k@ + 1)]
pub fn pick(o: Option<usize>, w: &[u32], k: u32) -> u32 {
    let _ = o.map(|j| if j < w.len() { w[j] } else { 0 });
    k + 1
}
