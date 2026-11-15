//@ expect: verify
//@ xfail: D-118's price. The closure guards its index by a CAPTURED length, `n`, that the host set
//@ xfail: to `w.len()`; verified under `requires true` the closure sees `n` and `w` as two
//@ xfail: unrelated captures. Creusot charges the closure's precondition at `Option::map` in the
//@ xfail: host, where `n == w.len()`.
//@ mechanism: a TRUE host whose closure's safety rests on a relation between two captures that only
//@ mechanism: the host establishes. option_map_guarded_closure_index_control guards by `w.len()`
//@ mechanism: itself and verifies; this one names what the captures-unconstrained rule costs.
//@ accept-means: n/a (control) — every index is guarded.
//@ fixed-by: n/a (control)
//@ teeth: control — `pick verified` on the binary before D-118; after it the closure is not
//@ teeth: verified and `pick`'s credit is withdrawn.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 1)]
pub fn pick(o: Option<usize>, w: &[u32]) -> u32 {
    let n = w.len();
    let _ = o.map(|j| if j < n { w[j] } else { 0 });
    1
}
