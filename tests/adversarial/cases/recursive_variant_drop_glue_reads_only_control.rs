//@ expect: verify
//@ mechanism: control for recursive_variant_reads_local_before_drop_glue_write: the same recursion, with
//@ mechanism: a guard whose `Drop` impl only reads. `m` stays 0, so each function recurses once and
//@ mechanism: must keep verifying.
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
#[variant(n@)]
pub fn scope_end(n: u32) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    {
        let _g = G(&mut m);
    }
    scope_end(m);
}

#[check(terminates)]
#[variant(n@)]
pub fn mem_drop(n: u32) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    let g = G(&mut m);
    std::mem::drop(g);
    mem_drop(m);
}
