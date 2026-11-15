//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: total
//@ mechanism: a callee's parameter type invariant owed by a call INSIDE an annotated loop body. The
//@ mechanism: per-loop obligation group charged the callee's written `requires` and nothing else, so
//@ mechanism: `total` was verified from `inv(s)` and the caller that built a broken `s` inside the
//@ mechanism: loop owed nothing.
//@ mechanism: A lane that charged the written `requires` alone and never read the callee's invariant
//@ mechanism: grant: `charge_callee_invariant_grant` is now the one charging step on every lane (D-141).
//@ accept-means: a type invariant is evaded by moving the call into a loop body.
//@ WHY THE CONTRACT IS FALSE: the call hands `total` a `Sum10` of 1 and 1, which breaks the invariant its
//@ WHY THE CONTRACT IS FALSE: parameter is granted: the call's precondition does not hold, and `total`'s body
//@ WHY THE CONTRACT IS FALSE: returns 2 where its postcondition says 10.
//@ teeth: MEASURED as a LIVE whole-run false accept on one build with the loop lanes' charge
//@ teeth: disabled by a local knob: `total verified`, `caller verified`, exit 0. Now `caller FAILED
//@ teeth: (loop call obligations)`.
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
pub fn caller(n: u32) -> i32 {
    let mut r = 10;
    let mut i = 0;
    #[invariant(r@ == 10)]
    while i < n {
        let s = Sum10 { a: 1, b: 1 };
        r = total(s);
        i += 1;
    }
    r
}
