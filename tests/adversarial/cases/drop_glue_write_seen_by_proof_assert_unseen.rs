//@ expect: reject
//@ mechanism: the proof_assert lane's spelling of drop_impl_write_through_held_mut_unseen: the
//@ mechanism: substitution walk followed a `Drop` terminator, and a call to `mem::drop`, without an
//@ mechanism: effect, so `c` kept its value before the borrow and `c@ == 0` was proved after the guard
//@ mechanism: ran.
//@ accept-means: a `proof_assert!` is credited although the guard's `Drop` impl has set the asserted local to
//@ accept-means: 5.
//@ WHY THE CONTRACT IS FALSE: at each assertion `c` is 5: the guard was dropped (at the end of its scope, and by
//@ WHY THE CONTRACT IS FALSE: `mem::drop`) and `G::drop` wrote it.
//@ fixed-by: D-140: the substitution walk re-binds what a writing drop reaches, at the `Drop` and on the
//@ fixed-by: return edge of a call handed the value.
//@ teeth: MEASURED: with D-140's hand-off disabled both assertions are `verified`; with it both are
//@ teeth: FAILED.
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

pub fn scope_end() {
    let mut c = 0u32;
    {
        let _g = G(&mut c);
    }
    proof_assert!(c@ == 0);
}

pub fn mem_drop() {
    let mut c = 0u32;
    let g = G(&mut c);
    std::mem::drop(g);
    proof_assert!(c@ == 0);
}
