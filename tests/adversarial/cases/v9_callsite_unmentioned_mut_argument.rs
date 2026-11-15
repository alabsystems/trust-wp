//@ expect: reject
//@ mechanism: `keep(v, &mut *p)` passes a reborrow of a reborrow of `p` to a callee whose clause
//@ mechanism: says nothing of its second argument. The two-phase writeback of the inner reborrow
//@ mechanism: into the outer one asserted `*outer == ^inner`, and `*outer` is also the value the
//@ mechanism: outer reborrow was taken at (`p`'s entry value), so the callee was assumed to leave
//@ mechanism: the argument unchanged. The gate that drops that writeback for a mutation-continued
//@ mechanism: parent named the parent alone, not the parameter its reborrow chain descends from.
//@ accept-means: a caller (or an assertion after the call) learns the final value of a `&mut`
//@ accept-means: argument from a callee clause that does not mention it.
//@ WHY THE CONTRACT IS FALSE: `keep` stores 7 through its second argument, so `^p` is 7 and the
//@ WHY THE CONTRACT IS FALSE: precondition makes the entry `*p` something else.
//@ fixed-by: D-107 (the delayed-writeback filters read the parent's reborrow-chain root,
//@ fixed-by: `formula::reborrow_root`; a spec-advanced call havocs its other `&mut` arguments)
//@ teeth: MEASURED (debug driver) on 576532d7: `keep verified`, `keep_caller verified` (the
//@ teeth: certificate chains `p_current == p$rb9_current == p$rb9$rb8_final == p_final`) and
//@ teeth: `keep_through_local verified`, and the proof_assert lane's twin `proof_assert in
//@ teeth: keep_assert verified`, `keep_assert verified`. On the D-107 tree all three are unknown.
//@ also-verified: keep
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^v == *v)]
pub fn keep(v: &mut i32, p: &mut i32) {
    *p = 7;
}

#[requires(*p != 7i32)]
#[ensures(^p == *p)]
pub fn keep_caller(v: &mut i32, p: &mut i32) {
    keep(v, &mut *p)
}

#[requires(*p != 7i32)]
#[ensures(^p == *p)]
pub fn keep_through_local(v: &mut i32, p: &mut i32) {
    let r = &mut *p;
    keep(v, r)
}

#[requires(*p != 7i32)]
pub fn keep_assert(v: &mut i32, p: &mut i32) {
    let before = *p;
    keep(v, &mut *p);
    proof_assert!(*p == before);
}
