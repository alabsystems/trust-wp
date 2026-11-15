//@ expect: reject
//@ mechanism: Iterator::collect spec — the `result@ == self@` view bridge must not reach non-roundtrip collects
//@ fixed-by: wp-s24 (ITERATOR_COLLECT split into gated ITERATOR_COLLECT_ROUNDTRIP)
//@ accept-means: the collect spec asserted a false relation between the collected value and its source. Refuting execution: (0..3) collects 3 elements, not 4.
//@ teeth: UNVERIFIED as a defect detector. Before the fix this case was rejected only by an accidental sort conflict on the ungated `result@ == self@` clause (audit 2026-09-12); after it, the clause is absent for this (Self, B) pair. Standing shape gate: if the bridge is ever re-widened with a sort that unifies, this contract becomes provable.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@.len() == 4)]
pub fn range_bad() -> Vec<u32> {
    let r: Vec<u32> = (0u32..3).collect();
    r
}
