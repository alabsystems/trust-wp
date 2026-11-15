//@ expect: reject
//@ mechanism: proof_assert twin of cp_cell_conflate.rs — the SUBSTITUTION lane re-derived
//@ mechanism: `inner(c)` from the pre-call receiver for both `c.get()` reads, so two reads
//@ mechanism: around `c.set(0)` were one term. The primary lane's s44 rule (bind an
//@ mechanism: interior-mutable read to the call's fresh result symbol) was never applied there.
//@ fixed-by: s63 (wp-s63, one shared interior-mutability decision for both extraction lanes)
//@ accept-means: `a == b` around `c.set(0)` discharged; false for any cell not holding 0.
//@ verdict: unknown
//@ teeth: on wp-campaign 04fc8074 (debug driver) this run exited 0 with
//@ teeth: `cell_conflate_assert verified ✓` AND `proof_assert in creusot_test::cell_conflate_assert
//@ teeth: verified ✓` — a live exit-0 false accept. On wp-s63 the assertion is no longer
//@ teeth: discharged (`proof_assert: 0 verified, 0 failed, 1 errors`, exit 2).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::cell::Cell;

#[ensures(true)]
pub fn cell_conflate_assert(c: &Cell<u8>) {
    let a = c.get();
    c.set(0);
    let b = c.get();
    proof_assert!(a == b);
}
