//@ expect: reject
//@ mechanism: a whole-local MOVE of a `&mut` borrow (`let r2 = r;`) is not a borrow-chain edge in the proof_assert substitution lane, so the write `*r2 = 7` reaches neither `r2`'s chain (it has none) nor `x`; `x` keeps its entry value. The same defect, with the move done by a call handing the borrow back, was K1 (`s84_ghost_deref_mut_handback`).
//@ fixed-by: wp-s84 (a whole-local move of a `&mut` joins the borrow chain at the place it governs; a reassigned borrow local drops its stale edge)
//@ accept-means: any `&mut` that is moved into another local freezes its pointee at the entry value for every later read — a plain-Rust false accept with no ghost code involved.
//@ WHY THE PROGRAM IS WRONG: `r2` is `r` is `&mut x`; `*r2 = 7` sets `x` to 7, and the assertion claims 5.
//@ teeth: LIVE on the campaign tip 684821d0: ACCEPTED, `proof_assert in creusot_test::k verified`,
//@ teeth: base_exit_code=0. Found by this
//@ teeth: front's probes while characterizing K1; PRE-EXISTING, not introduced here. With the move
//@ teeth: edge in place: FAILED with a counterexample, exit 1 on the same program.
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let r = &mut x;
    let r2 = r;
    *r2 = 7;
    proof_assert!(x == 5i32);
}
