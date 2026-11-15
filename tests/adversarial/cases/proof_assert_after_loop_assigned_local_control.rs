//@ expect: verify
//@ mechanism: control for proof_assert_after_loop_assigned_local_reads_pre_loop_value.rs: the same function asserts `t == x`, which holds after `t = x`. A fix that refuses every assertion after a loop rejects this.
//@ accept-means: n/a (control) — the assertion holds on every execution.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn prog(n: u32, x: u32) {
    let mut t = 0u32;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    t = x;
    proof_assert!(t == x);
}
