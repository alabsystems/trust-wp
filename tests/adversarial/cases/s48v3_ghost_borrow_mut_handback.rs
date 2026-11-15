//@ expect: reject
//@ mechanism: the `::Ghost::borrow_mut` entry of the ExternSpec borrow-forwarding allowlist — the same hazard as s48v3_ghost_inner_mut_handback, reached through `borrow_mut().into_inner()`.
//@ fixed-by: wp-s48 v3 (allowlist audit: `::Ghost::borrow_mut` deleted — it matched nothing in any corpus, and was a live exit-0 false accept)
//@ accept-means: `Ghost::borrow_mut` freezes the ghost cell at its entry value, so the write through the `&mut i32` reached from the returned borrow is invisible.
//@ WHY THE PROGRAM IS WRONG: `*b.into_inner() = 7` writes through the borrow of `g`'s payload that `borrow_mut` returned, so `*g` is 7 at the proof_assert; the assertion claims 5.
//@ teeth: A/B'd 2026-09-14 on this branch: re-adding ONLY `"::Ghost::borrow_mut"` to
//@ teeth: FORWARDING_SPEC_LIBRARY_SUFFIXES and rebuilding turns this case ACCEPTED
//@ teeth: (exit 0, `proof_assert ... verified ✓`); with the audited list it is `failed`
//@ teeth: with a counterexample. It also accepted on wp-campaign ce1d56fc and at
//@ teeth: 4c05ec5a, on a review probe of this same `borrow_mut().into_inner()` handback.
//@ teeth: With D-218 the counterexample is withheld, not printed: the borrow's final value is
//@ teeth: split by a sort upgrade after the assertion read it, so the model need not be an
//@ teeth: execution; D-218 acts on refutations only.
//@ verdict: unknown
//@ refused-with: proof_assert in creusot_test::k unknown (refutation withheld: a phantom sort upgrade split
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn k() {
    let mut g = ghost!(5i32);
    ghost! {
        let b = g.borrow_mut();
        *b.into_inner() = 7;
    };
    proof_assert!(*g == 5i32);
}
