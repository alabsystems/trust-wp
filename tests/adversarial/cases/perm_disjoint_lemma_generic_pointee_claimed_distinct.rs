//@ expect: reject
//@ mechanism: the generic twin of perm_disjoint_lemma_zero_sized_pointers_claimed_distinct: `g`'s
//@ mechanism: pointee is its own parameter `T`, which a caller may instantiate with a zero-sized type,
//@ mechanism: so no call inside `g` knows the pointee has a size. `f` calls `g` with `()`.
//@ accept-means: `g` proves `p1 != p2` for every `T`, false for `T = ()` where both `Perm::new`
//@ accept-means: pointers are the same dangling one.
//@ fixed-by: D-139 — a caller's generic pointee gets no disjointness fact.
//@ also-verified: f
//@ teeth: ACCEPTED (`proof_assert in creusot_test::g verified`, `g verified`, exit 0) when committed;
//@ teeth: `g` FAILED on the proof_assert under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn g<T>(a: T, b: T) {
    let (p1, mut own1) = Perm::new(a);
    let (p2, own2) = Perm::new(b);
    ghost! {
        let _ = Perm::disjoint_lemma(&mut own1, &own2);
    };
    proof_assert!(p1 != p2);
}

#[ensures(true)]
pub fn f() {
    g((), ());
}
