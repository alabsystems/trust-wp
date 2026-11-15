//@ expect: reject
//@ mechanism: the contract parser keeps a borrow as its operand, so `frozen(&mut (*y).0)` reaches the logic lane as `frozen((*y).0)`, and the callee's `^x == *x` substituted at it reads the final value of a place instead of the borrow the call makes. A call to a callee that takes a `&mut` parameter or whose precondition reads a final value is refused (`callee_preconditions::reads_a_final_value`).
//@ accept-means: a logic function that calls `frozen` on a reborrow whose final value is unconstrained is credited `verified`.
//@ WHY IT IS FALSE: nothing ties `^(*y).0` to `(*y).0`, and `frozen` requires them equal; Creusot's `vc_caller` owes that and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓`. With the lane owing the precondition and the refusal disabled: `caller FAILED ✗ (logic callee precondition)`; the same reading refutes lang/logic_vcgen.rs's `f`, whose precondition holds, so the call is refused rather than read.
//@ fixed-by: D-119
//@ verdict: error
//@ refused-with: reads a final value (`^`), which a logic parameter cannot carry
//@ note: since the owner's D-108 both logic functions are refused before D-119's lane runs: a logic function that reads `^` has no reading. D-119's own refusal ("whose precondition reads a final value or takes a `&mut` parameter") is the second line of defence behind it.
//@ note: no control: a TRUE call of this shape (lang/logic_vcgen.rs's `f`) is refused as well.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(prophetic)]
#[requires(^x == *x)]
pub fn frozen(x: &mut i32) -> Int {
    pearlite! { (*x)@ }
}

#[logic(prophetic)]
#[ensures(true)]
pub fn caller(y: &mut (i32, i32)) -> Int {
    frozen(&mut (*y).0)
}
