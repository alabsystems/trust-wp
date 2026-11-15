//@ expect: reject
//@ mechanism: a closure writing its `&mut` capture of a parameter reassigned before the closure is
//@ mechanism: built. Read off the capture's value (`a + 1`), the closure's `ensures(a@ == 7)` bound
//@ mechanism: no capture, and the call's credit stated it over the parameter's symbol, its ENTRY
//@ mechanism: value: it pinned the entry value to 7, and `result == b == 7` followed.
//@ accept-means: a closure's postcondition about a capture is credited to the caller's entry value.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: caller(0) returns 0, the entry value.
//@ verdict: unknown
//@ refused-with: final-collapse refused (fail-closed)
//@ also-verified: caller::{closure#3}
//@ fixed-by: fix(closure-call): a call binds each capture by the names the closure's own contract lane reads it by
//@ teeth: ACCEPTED at exit 0 without the fix named in `fixed-by:`; with the capture bound, the
//@ teeth: credit states the final value of `a + 1`, which the final-collapse guard refuses (D-14).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@ < 100)]
#[ensures(result@ == 7)]
pub fn caller(mut a: i32) -> i32 {
    let b = a;
    a = a + 1;
    let mut c = #[ensures(a@ == 7)]
    || {
        a = 7;
    };
    c();
    b
}
