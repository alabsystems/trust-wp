//@ expect: reject
//@ mechanism: the outer loop's body walk summarized an inner loop's `v[j] = 1` writes as ONE
//@ mechanism: point write `v@.set(k, 1)` at the index the walk last saw. The preservation VC
//@ mechanism: reads the off-index frame of a point write, `v'@[m] == v@[m]` for `m != k`, so
//@ mechanism: `v@[5] == 0u32` survived an inner loop that sets every element to 1.
//@ accept-means: `f(v, 1)` with `v@ == [0; 10]` leaves `v@[5] == 1` after one outer iteration,
//@ accept-means: so the outer invariant `v@[5] == 0u32` is FALSE, and trust-wp proved it preserved.
//@ fixed-by: D-220 (the outer body walk havocs everything an inner loop may write)
//@ teeth: before the fix ay answered UNSAT on the outer preservation VC, and only the strict
//@ teeth: certificate gate (`unknown (loop invariant: proof-trusted)`) kept it from `verified`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(v@.len() == 10)]
#[requires(v@[5] == 0u32)]
pub fn f(v: &mut Vec<u32>, n: u32) {
    let mut i = 0u32;
    #[invariant(v@.len() == 10)]
    #[invariant(v@[5] == 0u32)]
    while i < n {
        let mut j: usize = 0;
        #[invariant(v@.len() == 10)]
        while j < 10 { v[j] = 1; j += 1; }
        i += 1;
    }
}
