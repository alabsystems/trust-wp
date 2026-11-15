//@ expect: reject
//@ verdict: failed
//@ fn-failed: pred_lit
//@ mechanism: the tier-1 native QF_BV lane (bitwise_bv_proof) recovered W = 31 for an i32 from the
//@ mechanism: user's `x >= 0` plus the injected `x@ <= 2^31 - 1`, and encoded the body `x - 1` as an
//@ mechanism: UNGUARDED 31-bit `bvsub`. At x = 0 that is 2^31 - 1, not -1, so `bvuge(x - 1, 0)` is a
//@ mechanism: tautology and ay returned a genuine, strictly checked UNSAT certificate for a query that
//@ mechanism: does not match the program. The lane ran on ordinary (non-#[bitwise_proof]) functions
//@ mechanism: whenever any visible logic fn exists (here `zero`), and the spec side was a literal.
//@ accept-means: `pred_lit(0)` returns -1 (no i32 overflow), so `ensures(result >= 0)` is false.
//@ fixed-by: trust-wp fix(bv-lane): exactness-guard every wrapping node before a native BV Verified
//@ teeth: `pred_lit verified` (and `pred_logic verified`) on trust-wp 04c2aed9; `pred_lit FAILED`
//@ teeth: with cex x = 0 once each `-`/`+`/`*`/`<<`/neg node carries its wrap guard.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic(open)]
pub fn zero() -> Int {
    0
}

#[requires(x >= 0)]
#[ensures(result >= 0)]
pub fn pred_lit(x: i32) -> i32 {
    x - 1
}
