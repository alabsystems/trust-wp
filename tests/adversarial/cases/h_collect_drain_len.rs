//@ expect: reject
//@ mechanism: Iterator::collect spec — the `result@ == self@` view bridge must not reach non-roundtrip collects
//@ fixed-by: wp-s24 (ITERATOR_COLLECT split into gated ITERATOR_COLLECT_ROUNDTRIP)
//@ accept-means: the collect spec asserted a false relation between the collected value and its source. Refuting execution: drain(1..) of 3 elements collects 2.
//@ teeth: UNVERIFIED as a defect detector. Before the fix this case was rejected only by an accidental sort conflict on the ungated `result@ == self@` clause (audit 2026-09-12); after it, the clause is absent for this (Self, B) pair. Standing shape gate: if the bridge is ever re-widened with a sort that unifies, this contract becomes provable.
//@ note: D-121 refuses `drain(1..)` at the call (a range the spec cannot read), so the run is
//@ note: `unknown` before the collect is reached, and this shape gate is masked until the
//@ note: drain's range is read. `drain(..)` is read, but collects every element, so the bridge
//@ note: it gates would be true there.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 3)]
pub fn drain_bad(mut v: Vec<u32>) {
    let r: Vec<u32> = v.drain(1..).collect();
    proof_assert!(r@.len() == 3);
}
