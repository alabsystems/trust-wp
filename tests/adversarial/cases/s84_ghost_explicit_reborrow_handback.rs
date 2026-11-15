//@ expect: reject
//@ mechanism: the same allowlist entry as s84_ghost_deref_mut_handback, reached through the explicit reborrow `&mut *g` (which lowers to the same `<Ghost<T> as DerefMut>::deref_mut` call plus a reborrow of its result) instead of the method call.
//@ fixed-by: wp-s84 (the entry deleted; the list is empty — and the write now flows back: a reborrow of the handed-back result is chained to the cell, so the honest twin verifies)
//@ accept-means: `&mut *g` freezes the ghost cell at its entry value, so the write through the reborrow is invisible to every later read of `*g`.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` writes the cell `g`, so `*g` is 7 at the proof_assert; the assertion claims 5.
//@ teeth: A/B'd both sides: at 684821d0 ACCEPTED, base_exit_code=0
//@ teeth: on this explicit-reborrow ghost program; with the allowlist entry emptied, FAILED with a
//@ teeth: counterexample, exit 1 on the same program.
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut g = ghost!(5i32);
    ghost! {
        let r: &mut i32 = &mut *g;
        *r = 7;
    };
    proof_assert!(*g == 5i32);
}
