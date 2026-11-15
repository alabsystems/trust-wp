//@ expect: reject
//@ verdict: unknown
//@ also-verified: total
//@ mechanism: a callee's parameter type invariant owed by a call AFTER a loop, stated through the same
//@ mechanism: block collector as the pre-loop spelling.
//@ mechanism: A lane that charged the written `requires` alone and never read the callee's invariant
//@ mechanism: grant: `charge_callee_invariant_grant` is now the one charging step on every lane (D-141).
//@ accept-means: a type invariant is evaded by any call after a loop.
//@ WHY THE CONTRACT IS FALSE: the call hands `total` a `Sum10` of 1 and 1, which breaks the invariant its
//@ WHY THE CONTRACT IS FALSE: parameter is granted: the call's precondition does not hold, and `total`'s body
//@ WHY THE CONTRACT IS FALSE: returns 2 where its postcondition says 10.
//@ teeth: With the loop lanes' charge disabled by a local knob `caller` is unknown for an
//@ teeth: unrelated reason (a sort-coercion bridge in the negated goal), so this spelling was not
//@ teeth: a live false accept; it pins the charge. Now `caller FAILED` on `inv(s)`.
//@ teeth: At D-165 the post-loop return walk gives `result` no value when it is a call's result,
//@ teeth: so `caller` is `unknown (incomplete loop: no single post-loop return value)` charged or
//@ teeth: not, and this spelling pins only that it is not credited; the charge's FAILED is pinned
//@ teeth: by post_loop_callee_typeinv_uncharged_result_unused.
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
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let s = Sum10 { a: 1, b: 1 };
    total(s)
}
