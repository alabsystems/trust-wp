//@ expect: reject
//@ mechanism: the `::Ghost::new` entry of the ExternSpec borrow-forwarding allowlist. In the encoding `Ghost<T>` IS `T`, so a `&mut` moved into a Ghost comes straight back out of `into_inner` — the same handback hazard as `Box::new`, on the spec-library tier.
//@ fixed-by: wp-s48 v4 (allowlist audit: the ghost by-value identities deleted under the corrected reachability criterion)
//@ accept-means: `Ghost::new(&mut x)` freezes `x` at its entry value, so the write through the `&mut i32` that `into_inner` hands back is invisible to every later read of `x`.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` writes through the borrow of `x` the Ghost handed back, so `x` is 7 at the proof_assert; the assertion claims 5.
//@ teeth: A/B'd on this branch: re-adding ONLY `"::Ghost::new"` to
//@ teeth: FORWARDING_SPEC_LIBRARY_SUFFIXES and rebuilding turns this case ACCEPTED
//@ teeth: (exit 0, `proof_assert ... verified ✓`); with the audited list it is
//@ teeth: `unknown` (exit 2, fail-closed). It also accepted at wp-s48 b30c81b5
//@ teeth: on the probe spelling that moves a program-level `&mut` into `Ghost::new`.
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use creusot_std::ghost::Ghost;

pub fn k() {
    let mut x = 5i32;
    ghost! {
        let h = Ghost::new(&mut x);
        let r: &mut i32 = h.into_inner();
        *r = 7;
    };
    proof_assert!(x == 5i32);
}
