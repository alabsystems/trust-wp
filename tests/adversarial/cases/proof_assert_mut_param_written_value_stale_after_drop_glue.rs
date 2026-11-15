//@ expect: reject
//@ mechanism: the body writes a `&mut` parameter's pointee, then drop glue writes it again, then a
//@ mechanism: `proof_assert!` of the value the BODY wrote: `*x = 7; { let _g = G(&mut *x); }
//@ mechanism: proof_assert!((*x)@ == 7)`, where `G::drop` stores 5. The substitution walk kept the body's
//@ mechanism: store as the pointee's value across the `Drop`, so the stale 7 was asserted. The entry-value
//@ mechanism: spelling of the same body is proof_assert_param_entry_requires_revived_by_drop_glue.
//@ accept-means: a `proof_assert!` is credited with the value a `&mut` parameter's pointee held before drop
//@ accept-means: glue overwrote it.
//@ WHY THE CONTRACT IS FALSE: at the assertion `*x` is 5: the guard is dropped after `*x = 7` and `G::drop`
//@ WHY THE CONTRACT IS FALSE: stores 5 through the reborrow.
//@ fixed-by: D-140: the substitution walk re-binds what a writing drop reaches at the `Drop`.
//@ teeth: MEASURED on one binary with D-140's hand-off disabled by an env knob (never committed):
//@ teeth: ACCEPTED, exit 0; with the hand-off, the assertion and the function are FAILED.
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

#[requires((*x)@ == 0)]
pub fn host(x: &mut u32) {
    *x = 7;
    {
        let _g = G(&mut *x);
    }
    proof_assert!((*x)@ == 7);
}
