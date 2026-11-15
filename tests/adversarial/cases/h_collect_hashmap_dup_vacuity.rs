//@ expect: reject
//@ mechanism: Iterator::collect spec — the `result@ == self@` view bridge must not reach non-roundtrip collects
//@ fixed-by: wp-s24 (ITERATOR_COLLECT split into gated ITERATOR_COLLECT_ROUNDTRIP)
//@ accept-means: the collect spec asserted a false relation between the collected value and its source. Refuting execution: proof_assert!(false) after collecting duplicate keys; the old len==prod.len() body would make the premises contradictory.
//@ teeth: UNVERIFIED as a defect detector. Before the fix this case was rejected only by an accidental sort conflict on the ungated `result@ == self@` clause (audit 2026-09-12); after it, the clause is absent for this (Self, B) pair. Standing shape gate: if the bridge is ever re-widened with a sort that unifies, this contract becomes provable.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::collections::HashMap;

#[requires(v@.len() == 2 && v@[0].0@ == 1 && v@[1].0@ == 1 && v@[0].1@ == 10 && v@[1].1@ == 20)]
pub fn hm_dup_bad2(v: Vec<(u32, u32)>) {
    let _m: HashMap<u32, u32> = v.into_iter().collect();
    proof_assert!(false);
}
