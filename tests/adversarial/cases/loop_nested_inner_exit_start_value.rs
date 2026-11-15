//@ expect: reject
//@ mechanism: an inner loop resets `j` and runs it to 5; the outer body reads `j` before the inner
//@ mechanism: loop, at its value from the previous iteration (100 on the first). The inner loop's exit
//@ mechanism: facts (`j <= 5`, `!(j < 5)`) describe `j` AFTER it; asserted over the value the outer
//@ mechanism: iteration STARTS with, they make `j == 100` false and the store `k = 1` unreachable.
//@ accept-means: `f(1)` enters the outer body with `j == 100` and sets `k = 1`, so the outer invariant
//@ accept-means: `k == 0u32` is FALSE after the first iteration, and trust-wp proved it preserved.
//@ teeth: UNVERIFIED as a false-accept gate: rejected on every build measured. Before D-219 it was
//@ teeth: refuted `FAILED (loop invariant)`; since D-219 and D-220 a variable an inner loop writes is a
//@ teeth: premise the outer VC drops, and the refutation is withheld as `unknown`.
//@ teeth: loop_nested_inner_exit_start_value_control is its twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn f(n: u32) -> u32 {
    let mut i: u32 = 0;
    let mut j: u32 = 100;
    let mut k: u32 = 0;
    #[invariant(i <= n)]
    #[invariant(k == 0u32)]
    while i < n {
        if j == 100 { k = 1; }
        j = 0;
        #[invariant(j <= 5u32)]
        while j < 5 { j += 1; }
        i += 1;
    }
    k
}
