//@ expect: verify
//@ mechanism: control for loop_variant_reads_body_local_before_drop_glue_write: the same loops, with a
//@ mechanism: guard whose `Drop` impl only reads. `n` decreases by one each iteration, so each
//@ mechanism: function terminates and must keep verifying.
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

#[check(terminates)]
#[requires(true)]
pub fn scope_end() {
    let mut n = 10u32;
    #[variant(n@)]
    while n > 0 {
        let mut m = n - 1;
        {
            let _g = G(&mut m);
        }
        n = m;
    }
}

#[check(terminates)]
#[requires(true)]
pub fn mem_drop() {
    let mut n = 10u32;
    #[variant(n@)]
    while n > 0 {
        let mut m = n - 1;
        let g = G(&mut m);
        std::mem::drop(g);
        n = m;
    }
}
