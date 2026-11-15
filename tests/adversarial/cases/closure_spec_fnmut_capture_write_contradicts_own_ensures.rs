//@ expect: reject
//@ mechanism: the stronger spelling of closure_spec_fnmut_capture_write_unseen_by_caller: the
//@ mechanism: closure's own contract pins the capture's final value, `ensures(x@ == 50)`, and the
//@ mechanism: caller STILL reads `x` at its entry value 0 after the call. Neither the body's write
//@ mechanism: nor the postcondition that states it reaches the caller's binding of `x`.
//@ accept-means: a caller can contradict the postcondition of the closure it just called.
//@ fixed-by: OPEN — the caller's stale read of `x` stays (its twin is still ACCEPTED); outside D-104
//@ fixed-by: for the reason the twin states. Since a call binds each capture by the names the
//@ fixed-by: closure's own lane reads it by, the call's credit states `x`'s final value as 50 beside
//@ fixed-by: that stale read, and the vacuity guard refuses the contradictory premises.
//@ WHY THE CONTRACT IS FALSE: the closure sets `x` to 50, and says so in its contract; `f` returns
//@ WHY THE CONTRACT IS FALSE: `x`, so `result@ == 50`, not 0. The closure's own contract is TRUE,
//@ WHY THE CONTRACT IS FALSE: declared below.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, `f::{closure#2} verified ✓`; REFUSED
//@ teeth: since the capture-binding fix (`f vacuous (contradictory premises)`).
//@ verdict: error
//@ refused-with: f vacuous (contradictory premises)
//@ also-verified: f::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn f() -> u8 {
    let mut x = 0u8;
    let mut c = #[ensures(x@ == 50)]
    || {
        x = 50;
    };
    c();
    x
}
