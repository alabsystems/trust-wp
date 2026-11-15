//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ mechanism: the false half of the isolating pair for D-114: div_in_assumed_callee_spec_control
//@ mechanism: with the caller's goal changed from `result@ == 0` to `result@ == 1`. The assumed
//@ mechanism: trait contract pins the result of `safe_div(a, 0)` to 0, so dropping the divisor
//@ mechanism: obligation an assumed formula never owed must not let this goal through: only the
//@ mechanism: goal itself, refuted, rejects it.
//@ accept-means: the assumed contract's division was dropped together with the clause that pins
//@ accept-means: the zero-divisor result, or the goal was never asserted
//@ fixed-by: n/a (shape gate for D-114)
//@ teeth: shape gate — D-114 removes an obligation, so it moves only in the accept direction and
//@ teeth: this case is the one that must keep rejecting: FAILED with `a = 0, result = 0` before
//@ teeth: and after D-114. An impl returning 0 for divisor 0 honours the trait contract and makes
//@ teeth: `caller` return 0, not 1.
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

#[ensures(result@ == 1)]
pub fn caller<T: SafeDiv>(t: &T, a: u32) -> u32 {
    t.safe_div(a, 0)
}
