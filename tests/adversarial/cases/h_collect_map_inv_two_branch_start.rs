//@ expect: reject
//@ mechanism: map_inv collect view facts — two map_inv sources reaching ONE collect call site must not both be stated about its symbol as whole-function assumptions
//@ fixed-by: wp-s24 (collect-hardening-v3)
//@ accept-means: facts len == 7 - 0 and len == 7 - n held of one collect symbol, implying n == 0. Refuting execution: b = true, n = 3.
//@ teeth: Review of 24f026bc (probe review-probes/v2/b4): ay_result=unsat on this false contract; rejected ONLY by the strict-certificate gate (proof-trusted, exit 2). This case asserts ay is not unsat, so certificate gating cannot mask it.
//@ verdict: failed
//@ fn-failed: two
//@ ay-not-unsat: two
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// FALSE: n is unconstrained below 7.
#[requires(n <= 7u32)]
#[ensures(n == 0u32)]
pub fn two(b: bool, n: u32) {
    let c = |x: u32, _p: Snapshot<Seq<u32>>| x;
    let it = if b { (0u32..7).map_inv(c) } else { (n..7).map_inv(c) };
    let _v: Vec<u32> = it.collect();
}
