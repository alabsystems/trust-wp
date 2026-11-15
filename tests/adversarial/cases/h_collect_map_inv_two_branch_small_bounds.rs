//@ expect: reject
//@ mechanism: map_inv collect view facts — two map_inv sources reaching ONE collect call site must not both be stated about its symbol as whole-function assumptions
//@ fixed-by: wp-s24 (collect-hardening-v3)
//@ accept-means: both branch length facts held of one collect symbol under small bounds. Refuting execution: b = true, n = 0, m = 1.
//@ teeth: Review of 24f026bc (probe review-probes/v2/c2): ay_result=unsat on this false contract; rejected ONLY by the strict-certificate gate (proof-trusted, exit 2). This case asserts ay is not unsat, so certificate gating cannot mask it.
//@ verdict: failed
//@ fn-failed: two
//@ ay-not-unsat: two
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// FALSE: n = 0, m = 1 refutes.
#[requires(n <= 1usize && m <= 1usize)]
#[ensures(n == m)]
pub fn two(b: bool, n: usize, m: usize) {
    let c = |x: usize, _p: Snapshot<Seq<usize>>| x;
    let it = if b { (0usize..n).map_inv(c) } else { (0usize..m).map_inv(c) };
    let _v: Vec<usize> = it.collect();
}
