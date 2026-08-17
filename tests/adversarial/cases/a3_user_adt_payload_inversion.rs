//@ expect: reject
//@ mechanism: Final-collapse prophecy inversion on a USER ADT payload — rustc-backed AdtDecls
//@ mechanism: erase mutability (`&T` and `&mut T` both lower to ExprSort::Ref), so an
//@ mechanism: ADT-embedded `&mut` has no prophecy slot and the sort-blind routes collapse `^r`
//@ mechanism: onto the current-value carrier
//@ fixed-by: 932a7de (Fix A), generic-ADT refinement 9f835d7 (guardref)
//@ accept-means: the same inversion as a2, reached through a user-defined enum instead of a std
//@ accept-means: API. This is the shape behind the still-armed std axioms the audit listed
//@ accept-means: (GET_MUT_GENERIC, HASHMAP_ITER_MUT, CELL_SET) — an accept means the guard no
//@ accept-means: longer covers ADT-embedded `&mut` payloads and those axioms are live again.
//@
//@ WHY THE CONTRACT IS FALSE: `caller` writes 9 through the payload while `*r` is 7.
//@ teeth: UNVERIFIED (honest). Method (ii): Fix A disabled in-tree, A/B'd in one build. Rejects both
//@ teeth: ways: the erased `Ref` field lowers the payload to a plain Int (CE: `result = Filled(0)`),
//@ teeth: so `^r`/`*r` are unconstrained-distinct rather than fused. Standing SHAPE gate.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum Slot<'a> {
    Empty,
    Filled(&'a mut i32),
}

#[ensures(match result {
    Slot::Filled(r) => ^r == *r,
    Slot::Empty => true,
})]
pub fn fill(x: &mut i32) -> Slot<'_> {
    *x = 7;
    Slot::Filled(x)
}

// The refutation, in executable Rust: after this call `*r` is 7 and `^r` is 9.
pub fn caller() {
    let mut v = 0i32;
    if let Slot::Filled(r) = fill(&mut v) {
        *r = 9;
    }
}
