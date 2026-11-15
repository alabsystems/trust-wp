//@ expect: verify
//@ mechanism: control for the mut_param_final_after_loop_* cases: a store of the parameter `n` through the `&mut` parameter after an annotated loop, claiming `^x == n`. A fix that drops every post-loop final value rejects this.
//@ accept-means: n/a (control) — `prog` leaves `n` behind its parameter on every execution.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^x == n)]
pub fn prog(x: &mut u32, n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    *x = n;
}
