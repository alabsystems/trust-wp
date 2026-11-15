//@ expect: reject
//@ verdict: failed
//@ mechanism: `Sum10` carries `impl Invariant { a + b == 10 }`. `total` is verified WITH
//@ mechanism: `inv(s)` as a premise — that is what lets it prove `result@ == 10`. `caller`
//@ mechanism: hands it `Sum10 { a: 1, b: 1 }`, which breaks the invariant. The premise is
//@ mechanism: only sound if the CALL SITE owes it; a two-field struct is used so the
//@ mechanism: newtype-collapse path cannot be what decides the verdict.
//@ accept-means: the synthesized type-invariant precondition is a free grant — the callee
//@ accept-means: reasons from an invariant no caller ever has to establish.
//@ WHY THE CONTRACT IS FALSE: `caller` returns 1 + 1 = 2, and claims 10.
//@ teeth: MEASURED as ACCEPTED, exit 0, "2 verified, 0 failed" before the call-site
//@ teeth: obligation existed.
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
    total(Sum10 { a: 1, b: 1 })
}
