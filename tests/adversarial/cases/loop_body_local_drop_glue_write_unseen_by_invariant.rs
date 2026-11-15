//@ expect: reject
//@ mechanism: drop glue that writes a local declared INSIDE a loop body, read into a loop-carried local
//@ mechanism: before the back edge: `let mut m = 0; { let _g = G(&mut m); } n = m;` (and `mem::drop(g)`),
//@ mechanism: where `G::drop` stores 5 through the borrow. The loop body's effect walk
//@ mechanism: (`loops::body_effects`, `BodyExtractionCtx::extract_from_block`) follows a `Drop` and a
//@ mechanism: call to its target without re-binding what the glue reaches, so `n`'s end-of-iteration
//@ mechanism: value is read as `m`'s value before the glue (0) and `#[invariant(n@ == 0)]` is
//@ mechanism: "preserved". D-140 re-binds at a hand-off in the primary, proof_assert, post-loop and loop
//@ mechanism: arithmetic walks, and relied on `WriteSites` for the loop lanes; `WriteSites` havocs the
//@ mechanism: loop-carried locals a drop reaches (drop_glue_write_inside_loop_pinned), not a body-local
//@ mechanism: whose value flows into one. The same body with the store written directly (`m = 5`) is
//@ mechanism: refuted (`loop invariant`), and a `proof_assert!` of `m` after the drop in the body is
//@ mechanism: refuted with the hand-off (and accepted without it).
//@ accept-means: a loop invariant, and the postcondition read after the loop, are credited although the
//@ accept-means: drop glue in each iteration sets the local that the loop-carried value is copied from to 5.
//@ WHY THE CONTRACT IS FALSE: each function returns 5: the first iteration's glue stores 5 into `m`, and
//@ WHY THE CONTRACT IS FALSE: `n = m` makes `n` 5, so `n@ == 0` is not preserved.
//@ fixed-by: D-140: the loop-body walk forgets a body-local the body lends out where a `Drop` or a call
//@ fixed-by: may write it (`locals_changed_by_handoff`), so `n = m` reads a value nothing constrains.
//@ teeth: MEASURED on one binary with the walk's forgetting disabled by an env knob (never committed):
//@ teeth: ACCEPTED, exit 0, `scope_end` and `mem_drop` verified; with it, each is FAILED (`loop
//@ teeth: invariant`). Control: loop_body_local_drop_glue_reads_only_control (the same functions, a `Drop`
//@ teeth: that only reads), verified either way.
//@ also-verified: <G<'_> as std::ops::Drop>::drop
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

#[ensures(result@ == 0)]
pub fn scope_end() -> u32 {
    let mut n = 0u32;
    let mut i = 0u32;
    #[invariant(n@ == 0)]
    #[invariant(i@ <= 3)]
    while i < 3 {
        let mut m = 0u32;
        {
            let _g = G(&mut m);
        }
        n = m;
        i += 1;
    }
    n
}

#[ensures(result@ == 0)]
pub fn mem_drop() -> u32 {
    let mut n = 0u32;
    let mut i = 0u32;
    #[invariant(n@ == 0)]
    #[invariant(i@ <= 3)]
    while i < 3 {
        let mut m = 0u32;
        let g = G(&mut m);
        std::mem::drop(g);
        n = m;
        i += 1;
    }
    n
}
