//@ expect: reject
//@ verdict: failed
//@ mechanism: the RED twin of callee_typeinv_constructed_arg_letbound_control. The same
//@ mechanism: let-bound aggregate, built to BREAK `a + b == 10`. The unfold that made the
//@ mechanism: true twin dischargeable replaces the obligation with the invariant's own
//@ mechanism: defining body at the caller's components, so it must refute here for the
//@ mechanism: same reason it discharges there.
//@ accept-means: the unfold weakened the obligation instead of stating it — a caller could
//@ accept-means: launder a value that breaks the invariant by constructing it at the call.
//@ WHY THE CONTRACT IS FALSE: `caller` returns 1 + 1 = 2, and claims 10.
//@ teeth: the twin control verifies, so the refutation here is the invariant's content and
//@ teeth: not an undischargeable obligation.
//@ also-verified: total
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

#[ensures(result@ == 10)]
pub fn total(s: Sum10) -> i32 {
    s.a + s.b
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    let v = Sum10 { a: 1, b: 1 };
    total(v)
}
