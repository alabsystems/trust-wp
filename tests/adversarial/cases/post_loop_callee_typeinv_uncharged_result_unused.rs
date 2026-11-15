//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: total
//@ mechanism: the spelling of post_loop_callee_typeinv_uncharged whose function-level check has a value
//@ mechanism: for `result`: the call after the loop hands `total` a `Sum10` that breaks its invariant and
//@ mechanism: its result is unused, so the post-loop return walk binds `result` to `10` (D-165 leaves
//@ mechanism: `result` unbound when it is a call's result, which makes the sibling `unknown`). The
//@ mechanism: call's invariant charge is the only goal here that can be false.
//@ accept-means: a type invariant is evaded by any call after a loop.
//@ WHY THE CONTRACT IS FALSE: the call hands `total` a `Sum10` of 1 and 1, which breaks the invariant its
//@ WHY THE CONTRACT IS FALSE: parameter is granted, so the call's precondition does not hold.
//@ teeth: `caller FAILED` at the campaign tip and at D-165. Argued, not measured with the charge
//@ teeth: disabled: `caller`'s postcondition holds and nothing reads `total`'s result, so an
//@ teeth: uncharged lane leaves no false goal and credits `caller`. A FAILED here does not show the
//@ teeth: charge is complete: the post-loop lane refutes it with `s` arbitrary, which is why the
//@ teeth: value twins of post_loop_callee_typeinv_uncharged are `xfail`.
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
    let _r = total(s);
    10
}
