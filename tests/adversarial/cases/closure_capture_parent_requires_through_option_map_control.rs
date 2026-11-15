//@ expect: verify
//@ xfail: D-118's price. The escaping closure is verified under `requires true` with its captures
//@ xfail: unconstrained, so the host's `k < w.len()` never reaches it; Creusot charges the
//@ xfail: closure's precondition at `Option::map` in the host, where the `requires` holds.
//@ mechanism: the TRUE twin of closure_capture_overwritten_before_escape_uncharged: the same host and
//@ mechanism: closure without the overwrite, so the captured `k` is the entry `k` the `requires`
//@ mechanism: bounds. Creusot proves it.
//@ accept-means: n/a (control) — `k < w.len()` holds when the closure runs.
//@ fixed-by: n/a (control)
//@ teeth: control — `pick verified` on the binary before D-118; after it the closure is not
//@ teeth: verified and `pick`'s credit is withdrawn. It verifies again only when the closure's
//@ teeth: obligations are charged at the hand-off under the host's facts.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k@ < w@.len())]
#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>, w: &[u32], k: usize) -> u32 {
    let _ = o.map(|_x| w[k]);
    1
}
