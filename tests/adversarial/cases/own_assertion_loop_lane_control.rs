//@ expect: verify
//@ mechanism: control for own_assertion_refuted_loop_lane.rs: the same loop-lane function with a TRUE assertion (the loop-exit premise proves it) keeps its credit
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ < 1000)]
pub fn count_up(n: u32) {
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        i += 1;
    }
    proof_assert!(i@ == n@ + 0);
}
