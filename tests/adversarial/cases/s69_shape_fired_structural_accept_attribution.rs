//@ expect: reject
//@ verdict: failed
//@ fn-failed: g7
//@ ay-not-unsat: g7
//@ mechanism: attribution twin of `s69_shape_fired_structural_accept`. SAME inconsistent `#[requires(fact(3) == 5)]`, but the postcondition is `fact(3) == 7`, which the recursive-EVALUATION accept lane cannot match — so the slice reached the real negated-goal solve even while the structural accept lanes were reachable. Pins the invariant the defect broke: the verdict must not depend on WHICH structural lane happens to match a slice a refutation shape has already refuted.
//@ accept-means: the same as its twin — a structural lane discharging a slice trust-wp's own shape refuted. If this case ever diverges from `s69_shape_fired_structural_accept`, the shape-fired slice is being decided by lane selection again.
//@ fixed-by: n/a — rejected before and after wp-s69 v2; it is the A/B partner that attributed the twin's accept to the shape no longer returning
//@ teeth: UNVERIFIED as a standalone defect gate — this case was ALREADY rejected (`g7 FAILED ✗`, exit 1) on the defective build wp-s69 81458208. Its teeth are differential: on that build its twin was ACCEPTED, so the pair is the gate.
//@ also-verified: creusot_test::fact
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
#[variant(n)]
#[requires(n >= 0)]
pub fn fact(n: Int) -> Int {
    pearlite! { if n <= 0 { 1 } else { n * fact(n - 1) } }
}

#[requires(fact(3) == 5)]
#[ensures(fact(3) == 7)]
pub fn g7(x: i32) -> i32 {
    x
}
