//@ expect: reject
//@ mechanism: a binder over references to `u8`: `forall<r: &u8> (*r)@ < 256` holds of every `&u8`. If the
//@ mechanism: referent is read over the unbounded integers the quantifier is false, and `f`, which
//@ mechanism: returns false, is credited.
//@ fixed-by: D-204 — the referent's range is stated on the body, as a machine integer binder's own
//@ fixed-by: is (D-203, which refused the binder).
//@ accept-means: `f` claims `result == true` in Rust's reading, returns false, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-202 in force.
//@ teeth: With D-203: REFUSED (`unknown`): `f` errors on the marker `__lfidU__r__binder__range`.
//@ teeth: With D-204: FAILED (`f FAILED ✗ (postcondition)`, counterexample `result = false`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (forall<r: &u8> (*r)@ < 256))]
pub fn f() -> bool {
    false
}
