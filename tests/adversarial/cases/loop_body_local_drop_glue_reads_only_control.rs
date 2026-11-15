//@ expect: verify
//@ mechanism: control for loop_body_local_drop_glue_write_unseen_by_invariant: the same loops, with a
//@ mechanism: guard whose `Drop` impl only reads through the borrow. `m` stays 0, so `n@ == 0` is
//@ mechanism: preserved and each function must keep verifying.
//@ accept-means: n/a (control)
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        let _ = *self.0;
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
