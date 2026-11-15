//@ expect: reject
//@ mechanism: the `FnOnce` spelling of closure_spec_fnmut_capture_write_unseen_by_caller. The
//@ mechanism: closure moves `v` out of its environment, so it is `FnOnce` and the call is
//@ mechanism: `FnOnce::call_once`, not `FnMut::call_mut`; it still captures `x` by unique borrow and
//@ mechanism: sets it to 250. After `c()` the caller reads `x` at its entry value 0, so its
//@ mechanism: `ensures(result@ == 0)` verifies. A fix for the `FnMut` twin that keys on
//@ mechanism: `call_mut` leaves this spelling open. A clause-free caller that does arithmetic on
//@ mechanism: `x` after the same call is refuted instead (`x` is havocked there), so D-104's credit
//@ mechanism: for `call_once` does not reach this; the postcondition lane does.
//@ accept-means: any claim about a captured variable's value before a spec-bearing `FnOnce` call
//@ accept-means: survives the call whatever the closure wrote.
//@ fixed-by: OPEN — committed RED rather than hidden; the same defect as
//@ fixed-by: closure_spec_fnmut_capture_write_unseen_by_caller, reached through `call_once`.
//@ WHY THE CONTRACT IS FALSE: the closure sets `x` to 250 and `f` returns `x`, so `result@ == 250`,
//@ WHY THE CONTRACT IS FALSE: not 0. The closure's own `ensures(true)` is TRUE, declared below.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, `f::{closure#2} verified ✓`.
//@ also-verified: f::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct NotCopy(pub u8);

#[ensures(result@ == 0)]
pub fn f() -> u8 {
    let mut x: u8 = 0;
    let v = NotCopy(1);
    let c = #[ensures(true)]
    || {
        let _w = v;
        x = 250;
    };
    c();
    x
}
