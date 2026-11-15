//@ expect: reject
//@ mechanism: a local declared INSIDE a loop body, handed `&mut` to a verified callee whose postcondition
//@ mechanism: fixes its final value (`set5`: `(^x)@ == 5`), then copied into a loop-carried local before the
//@ mechanism: back edge: `let mut m = ..; set5(&mut m); n = m;`. The loop body's effect walk
//@ mechanism: (`loops::body_effects`, `BodyExtractionCtx::extract_from_block`) follows a call to its target
//@ mechanism: binding nothing the callee wrote through its `&mut` argument, so `n`'s end-of-iteration value
//@ mechanism: is `m`'s value before the call. `invariant_kept` is credited `n@ == 0` preserved and returns
//@ mechanism: `n` as 0; `variant_decreases` is credited `n` decreasing under `#[check(terminates)]`. The same
//@ mechanism: call handed the loop-carried `&mut n` directly is refuted (`WriteSites` havocs `n`), as is the
//@ mechanism: store written as `m = 5` or `let r = &mut m; *r = 5`. Found probing D-140's loop spelling
//@ mechanism: (loop_body_local_drop_glue_write_unseen_by_invariant is the same walk at a `Drop`); not a drop.
//@ accept-means: a loop invariant, a postcondition read after the loop, and a loop variant are credited
//@ accept-means: against a body-local's value before a callee that the walk was told writes it.
//@ WHY THE CONTRACT IS FALSE: `invariant_kept` returns 5 (`n = m` after `set5` stores 5). From `n = 10`,
//@ WHY THE CONTRACT IS FALSE: `variant_decreases` sets `n` to 5 on every iteration: the loop never exits.
//@ fixed-by: D-140: the loop-body walk forgets every lent body-local after a call handed an argument it
//@ fixed-by: may write through (`call_may_write_through_args`), the callee's `^` being bound by no walk.
//@ teeth: MEASURED on one binary with the walk's forgetting disabled by an env knob (never committed):
//@ teeth: ACCEPTED, exit 0, `invariant_kept` and `variant_decreases` verified; with it, each is FAILED
//@ teeth: (`loop invariant`). Neither body holds drop glue that may write, so no hand-off reaches it.
//@ also-verified: set5
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[ensures((^x)@ == 5)]
pub fn set5(x: &mut u32) {
    *x = 5;
}

#[ensures(result@ == 0)]
pub fn invariant_kept() -> u32 {
    let mut n = 0u32;
    let mut i = 0u32;
    #[invariant(n@ == 0)]
    #[invariant(i@ <= 3)]
    while i < 3 {
        let mut m = 0u32;
        set5(&mut m);
        n = m;
        i += 1;
    }
    n
}

#[check(terminates)]
#[requires(true)]
pub fn variant_decreases() {
    let mut n = 10u32;
    #[variant(n@)]
    while n > 0 {
        let mut m = n - 1;
        set5(&mut m);
        n = m;
    }
}
