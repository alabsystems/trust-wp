//@ expect: reject
//@ mechanism: a writing guard dropped inside a loop body, with an invariant that claims the borrowed local
//@ mechanism: is unchanged. The loop lanes already count a `Drop` of a value that may carry a write
//@ mechanism: capability as a write to whatever it reaches (`WriteSites`), so the invariant's preservation
//@ mechanism: reads `c` fresh; this pins that D-140 did not have to, and must not undo it.
//@ accept-means: a loop invariant is credited although the guard dropped in each iteration sets `c` to 5.
//@ WHY THE CONTRACT IS FALSE: for `n >= 1`, `c` is 5 after the first iteration, so the invariant `c@ == 0` fails to be
//@ WHY THE CONTRACT IS FALSE: preserved.
//@ fixed-by: n/a: rejected before and after D-140 (FAILED, loop invariant).
//@ teeth: UNVERIFIED as a gate of D-140: the parent rejects it too. It pins the loop lanes' reading of
//@ teeth: a drop.
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

#[requires(n@ < 10)]
#[ensures(result@ == 0)]
pub fn host(n: u32) -> u32 {
    let mut c = 0u32;
    let mut i = 0u32;
    #[invariant(c@ == 0)]
    #[invariant(i@ <= n@)]
    while i < n {
        {
            let _g = G(&mut c);
        }
        i += 1;
    }
    c
}
