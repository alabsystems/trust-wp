//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: the D-141 generic hop inside an annotated loop body: `via(s)` fixes `T = Sum10`, and the
//@ mechanism: per-loop obligation group owed none of `via`'s grant.
//@ mechanism: A lane that charged the written `requires` alone and never read the callee's invariant
//@ mechanism: grant: `charge_callee_invariant_grant` is now the one charging step on every lane (D-141).
//@ accept-means: a type invariant is evaded by moving the generic hop into a loop body.
//@ WHY THE CONTRACT IS FALSE: `caller` builds a `Sum10` of 1 and 1 in the loop, the impl returns 2 through
//@ WHY THE CONTRACT IS FALSE: `via`, and `caller` claims 10 whenever the loop runs.
//@ teeth: MEASURED as a LIVE whole-run false accept on one build with the loop lanes' charge
//@ teeth: disabled by a local knob: `via verified`, `caller verified`, exit 0. Now `caller FAILED
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


pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(n: u32) -> i32 {
    let mut r = 10;
    let mut i = 0;
    #[invariant(r@ == 10)]
    while i < n {
        let s = Sum10 { a: 1, b: 1 };
        r = via(s);
        i += 1;
    }
    r
}
