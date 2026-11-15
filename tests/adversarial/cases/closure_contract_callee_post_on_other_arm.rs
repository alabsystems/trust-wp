//@ expect: reject
//@ mechanism: the closure spelling of an arm premise (D-169): a closure carrying its own `ensures` calls
//@ mechanism: `below(x)` on one arm of its body. The closure's contract is checked by the primary walk of
//@ mechanism: its own body, so the premise must be scoped there as in a function.
//@ accept-means: a closure is verified from a callee postcondition on an execution that never calls it,
//@ accept-means: and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: the closure called as `c(200, false)` returns with `x == 200`.
//@ teeth: ACCEPTED at the campaign tip; rejected with D-169.
//@ verdict: failed
//@ fn-failed: host::{closure#1}
//@ also-verified: below, host
//@ fixed-by: D-169 (each premise an arm walk records is scoped to that arm's edge).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100 && result == x)]
pub fn below(x: u32) -> u32 {
    #[invariant(true)]
    while x >= 100 {}
    x
}

pub fn host(x: u32, flag: bool) {
    let c = #[ensures(x@ < 100)] |x: u32, flag: bool| { if flag { below(x); } };
    c(x, flag);
}
