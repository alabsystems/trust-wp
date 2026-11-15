//@ expect: verify
//@ mechanism: the TRUE twin of perm_disjoint_lemma_zero_sized_pointers_claimed_distinct: an `i32`
//@ mechanism: has a size, so two live boxes of one are two addresses, and Creusot's lemma gives
//@ mechanism: `p1 != p2`.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `proof_assert in creusot_test::f verified`, exit 0, when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() {
    let (p1, mut own1) = Perm::new(1i32);
    let (p2, own2) = Perm::new(2i32);
    ghost! {
        let _ = Perm::disjoint_lemma(&mut own1, &own2);
    };
    proof_assert!(p1 != p2);
}
