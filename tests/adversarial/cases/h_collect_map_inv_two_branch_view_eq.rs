//@ expect: reject
//@ mechanism: map_inv collect view facts — two map_inv sources reaching ONE collect call site must not both be stated about its symbol as whole-function assumptions
//@ fixed-by: wp-s24 (collect-hardening-v3)
//@ accept-means: both branch length facts held of one collect symbol, implying n@ == m@. Refuting execution: b = false, n = 3, m = 4.
//@ teeth: Review of 24f026bc (probe review-probes/v2/a1): ay_result=unsat on this false contract; rejected ONLY by the strict-certificate gate (proof-trusted, exit 2). This case asserts ay is not unsat, so certificate gating cannot mask it.
//@ verdict: failed
//@ fn-failed: two
//@ ay-not-unsat: two
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// FALSE: n and m are unrelated parameters.
#[requires(n@ <= 100 && m@ <= 100)]
#[ensures(n@ == m@)]
pub fn two(b: bool, n: u32, m: u32) -> u32 {
    let c = |x: u32, _p: Snapshot<Seq<u32>>| x;
    let it = if b { (0u32..n).map_inv(c) } else { (0u32..m).map_inv(c) };
    let v: Vec<u32> = it.collect();
    let _ = v;
    0
}
