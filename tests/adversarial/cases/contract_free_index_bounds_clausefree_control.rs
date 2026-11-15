//@ expect: verify
//@ mechanism: the isolating over-refusal control for contract_free_index_bounds_uncharged: the SAME
//@ mechanism: clause-free host indexing the SAME slice by the SAME parameter, with the index guarded
//@ mechanism: by `i < v.len()`. Clause-free on purpose — contract_free_index_bounds_control carries
//@ mechanism: a contract and is therefore a verification target by the ordinary route, so it
//@ mechanism: cannot tell a discovery rule that CHARGES a bounds check from one that refuses every
//@ mechanism: body that indexes. This body is a target only because the discovery predicate reads
//@ mechanism: the `Assert(BoundsCheck)` terminator, and it still verifies: the bounds goal is
//@ mechanism: stated under the guard and discharged, the site is recorded as charged by a kept
//@ mechanism: lane so `unchecked_panic_sites` leaves it out of the clause-free cap, and
//@ mechanism: `<[T]>::len` is a total core method that cannot panic.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `hop verified ✓`, exit 0. Its twin with the guard weakened to `<=`,
//@ teeth: contract_free_index_bounds_off_by_one, reports `hop FAILED`, so the pair separates a
//@ teeth: charge that discharges from a blanket refusal of indexing bodies (D-95).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

pub fn hop(v: &[u32], i: usize) -> u32 {
    if i < v.len() { v[i] } else { 0 }
}
