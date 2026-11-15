//@ expect: reject
//@ mechanism: the `::Ghost::inner_mut` entry of the ExternSpec borrow-forwarding allowlist — a listed callee that RETURNS a live `&mut` reborrow of its receiver, so suppressing the receiver's advance drops the caller's write through the borrow it was handed.
//@ fixed-by: wp-s48 v3 (allowlist audit: `::Ghost::inner_mut` deleted — it matched nothing in the should_succeed, should_fail or adversarial corpora, and was a live exit-0 false accept)
//@ accept-means: `Ghost::inner_mut` freezes the ghost cell at its entry value, so a write through the `&mut i32` it returns is invisible to every later read of the cell.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` writes through the borrow of `g`'s payload that `inner_mut` returned, so `*g` is 7 at the proof_assert; the assertion claims 5.
//@ teeth: A/B'd 2026-09-14 on this branch: re-adding ONLY `"::Ghost::inner_mut"` to
//@ teeth: FORWARDING_SPEC_LIBRARY_SUFFIXES and rebuilding turns this case ACCEPTED
//@ teeth: (exit 0, `proof_assert ... verified ✓`); with the audited list it is `failed`
//@ teeth: with a counterexample. It also accepted on wp-campaign ce1d56fc and at
//@ teeth: 4c05ec5a, measured on a review probe of the bare `inner_mut` handback,
//@ teeth: so the hole is older than this front.
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
        let r: &mut i32 = g.inner_mut();
        *r = 7;
    };
    proof_assert!(*g == 5i32);
}
