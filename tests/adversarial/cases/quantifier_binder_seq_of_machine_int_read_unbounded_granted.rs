//@ expect: reject
//@ mechanism: a binder over sequences of `u8`: no `Seq<u8>` has an element of 300, so `exists<s:
//@ mechanism: Seq<u8>> s.len() == 1 && s[0]@ == 300` is false. If the binder is read as a sequence
//@ mechanism: of unbounded integers it holds, and `f`, which returns true, is credited.
//@ fixed-by: D-203 — REFUSED: a binder whose type holds a machine integer other than as itself is
//@ fixed-by: spelled with the refusal marker, since the sort it maps to keeps no range for it.
//@ accept-means: `f` claims `result == false` in Rust's reading, returns true, and the crate exits 0.
//@ teeth: not shown: `unknown` (refutation withheld) with D-202 in force, where the elements were
//@ teeth: read unbounded. With D-203: REFUSED (`unknown`): `f` errors on the marker
//@ teeth: `__lfidU__s__binder__range`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (exists<s: Seq<u8>> s.len() == 1 && s[0]@ == 300))]
pub fn f() -> bool {
    true
}
