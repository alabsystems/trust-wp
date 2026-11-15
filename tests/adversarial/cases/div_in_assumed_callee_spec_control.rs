//@ expect: verify
//@ mechanism: the over-refusal half of the isolating pair for D-114. A trait method's contract
//@ mechanism: `(y@ != 0) ==> result@ == x@ / y@` and `(y@ == 0) ==> result@ == 0` is ASSUMED at a
//@ mechanism: call with divisor 0. The division sits inside an assumed formula, where Pearlite
//@ mechanism: division is total and owes nothing; the call's own divisor is never executed. The
//@ mechanism: encoder collected `y != 0` from the assumption with no guard, so the caller's goal
//@ mechanism: became `0 != 0` and a true contract was refuted with a validated counterexample.
//@ mechanism: The trait method has no body and no impl, so the only verification target is the
//@ mechanism: caller and nothing but the assumed contract decides it.
//@ accept-means: n/a (control) — this contract is TRUE: at `y == 0` the second clause gives 0.
//@ fixed-by: D-114
//@ teeth: FAILED ✗ (postcondition) with counterexample `a = 0` before D-114, `caller verified ✓`
//@ teeth: after it; the false twin div_in_assumed_callee_spec_false_goal.rs is FAILED on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait SafeDiv {
    #[ensures(y@ != 0 ==> result@ == x@ / y@)]
    #[ensures(y@ == 0 ==> result@ == 0)]
    fn safe_div(&self, x: u32, y: u32) -> u32;
}

#[ensures(result@ == 0)]
pub fn caller<T: SafeDiv>(t: &T, a: u32) -> u32 {
    t.safe_div(a, 0)
}
