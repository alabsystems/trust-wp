//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: total
//@ mechanism: a callee's parameter type invariant owed by a call inside a loop with NO invariant.
//@ mechanism: The unannotated-loop walker charged the written `requires` alone.
//@ mechanism: A lane that charged the written `requires` alone and never read the callee's invariant
//@ mechanism: grant: `charge_callee_invariant_grant` is now the one charging step on every lane (D-141).
//@ accept-means: a type invariant is evaded by moving the call into a loop without an invariant.
//@ WHY THE CONTRACT IS FALSE: the call hands `total` a `Sum10` of 1 and 1, which breaks the invariant its
//@ WHY THE CONTRACT IS FALSE: parameter is granted: the call's precondition does not hold, and `total`'s body
//@ WHY THE CONTRACT IS FALSE: returns 2 where its postcondition says 10.
//@ teeth: MEASURED on one build with the loop lanes' charge disabled by a local knob: `caller`
//@ teeth: verified. Now `caller` is refuted on the guarded `inv(Sum10(1, 1))`.
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
    let mut i = 0;
    while i < n {
        let s = Sum10 { a: 1, b: 1 };
        let _r = total(s);
        i += 1;
    }
    10
}
