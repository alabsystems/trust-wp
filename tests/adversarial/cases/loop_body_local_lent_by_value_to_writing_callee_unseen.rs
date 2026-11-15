//@ expect: reject
//@ mechanism: loop_body_local_written_by_callee_unseen with the loan held BELOW the top of a by-value
//@ mechanism: argument: `let mut m = 0; poke(H(&mut m)); n = m;` inside the loop body, where `H` has no
//@ mechanism: `Drop` impl and the verified `poke` stores 5 through `h.0`. The loop body's effect walk binds
//@ mechanism: nothing a callee writes, so `n`'s end-of-iteration value was `m`'s value before the call, and
//@ mechanism: `#[invariant(n@ == 0)]` was "preserved". No glue runs, so no hand-off re-binds `m`.
//@ accept-means: a loop invariant, and the postcondition read after the loop, are credited against a
//@ accept-means: body-local's value before a callee handed a loan of it inside a struct wrote it.
//@ WHY THE CONTRACT IS FALSE: `poke` stores 5 into `m` and `n = m`, so the function returns 5.
//@ fixed-by: D-140: the loop-body walk forgets every lent body-local after a call handed an argument it may
//@ fixed-by: write through (`call_may_write_through_args`).
//@ teeth: MEASURED on one binary with the walk's forgetting disabled by an env knob (never committed):
//@ teeth: ACCEPTED, exit 0, `loop_struct_loan verified`; with it, FAILED (`loop invariant`).
//@ also-verified: poke
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct H<'a>(pub &'a mut u32);

#[check(terminates)]
#[ensures(true)]
pub fn poke(h: H<'_>) {
    *h.0 = 5;
}

#[ensures(result@ == 0)]
pub fn loop_struct_loan() -> u32 {
    let mut n = 0u32;
    let mut i = 0u32;
    #[invariant(n@ == 0)]
    #[invariant(i@ <= 3)]
    while i < 3 {
        let mut m = 0u32;
        poke(H(&mut m));
        n = m;
        i += 1;
    }
    n
}
