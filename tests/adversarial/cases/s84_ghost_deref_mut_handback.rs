//@ expect: reject
//@ mechanism: the last surviving entry of the ExternSpec borrow-forwarding allowlist, `std::ops::DerefMut::deref_mut` on a ghost receiver (MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND). `<Ghost<T> as DerefMut>::deref_mut` returns `&mut self.0`, a live `&mut` reborrow of the receiver, so suppressing the receiver's advance is sound only if the caller's write through the handed-back borrow flows back to the receiver — and it does not: the write is recorded against the handed-back local (`*r == 7`) while `g` keeps its pre-block value.
//@ fixed-by: wp-s84 (the entry deleted; the list is empty — and the write now flows back: the `deref_mut` result of a ghost cell is chained to the cell itself, so the honest twin verifies)
//@ accept-means: `g.deref_mut()` freezes the ghost cell at its entry value for every later read, so a write through the borrow it hands back is invisible to `proof_assert!(*g == ..)`.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` writes the cell `g` through the borrow `deref_mut` handed back, so `*g` is 7 at the proof_assert; the assertion claims 5.
//@ teeth: A/B'd at the campaign tip 684821d0 (entry present): ACCEPTED,
//@ teeth: `proof_assert in creusot_test::k verified`, base_exit_code=0
//@ teeth: — with the list emptied and nothing else
//@ teeth: changed, `proof_assert in creusot_test::k FAILED` with a counterexample, exit 1
//@ teeth: PRE-EXISTING: docs/soundness.md
//@ teeth: carried it as K1, measured on 2026-09-14.
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::DerefMut;

pub fn k() {
    let mut g = ghost!(5i32);
    ghost! { let r = g.deref_mut(); *r = 7; };
    proof_assert!(*g == 5i32);
}
