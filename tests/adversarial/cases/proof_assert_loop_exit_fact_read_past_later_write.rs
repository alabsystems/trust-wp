//@ expect: reject
//@ mechanism: a loop's exit facts read at a `proof_assert!` after a LOCAL the facts name was re-bound past
//@ mechanism: the loop: `#[invariant(i@ <= 3)] while i < 3 { i += 1; } i = j; proof_assert!(j@ <= 3)`. The
//@ mechanism: assertion's premises carry the invariant and the negated condition as facts about `i` at the
//@ mechanism: loop's exit, and read them through the assertion's substitution (`i -> j`, and the fact
//@ mechanism: `i == j`), so `i@ <= 3` becomes a fact about `j`. D-140 withdraws these facts for a PARAMETER
//@ mechanism: the body re-binds (proof_assert_param_rebind_reads_entry_requires's `after_loop`); a local is
//@ mechanism: not asked. Found probing D-140's loop-exit withdrawal sideways; no drop is involved.
//@ accept-means: a `proof_assert!` is credited from a loop invariant about a local after the local was
//@ accept-means: overwritten, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `j` is the parameter, which nothing bounds; `loop_exit_reassign(7)` asserts
//@ WHY THE CONTRACT IS FALSE: `7 <= 3`.
//@ fixed-by: OPEN: committed RED. Closing it means withdrawing a loop-exit fact that names a local written
//@ fixed-by: between the loop's exit and the assertion, which needs that span of the body, not the
//@ fixed-by: assertion's substitution alone.
//@ teeth: LIVE at D-140's head: ACCEPTED, exit 0, `proof_assert in creusot_test::loop_exit_reassign verified`
//@ teeth: and `loop_exit_reassign verified`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
pub fn loop_exit_reassign(j: u32) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    i = j;
    proof_assert!(j@ <= 3);
    let _ = i;
}
