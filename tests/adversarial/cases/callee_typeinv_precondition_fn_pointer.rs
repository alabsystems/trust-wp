//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ mechanism: the callee is reached through a reified fn POINTER, so the call operand is a
//@ mechanism: local and not a constant the call's generic arguments can be read off. The
//@ mechanism: obligation has to come from the callee's own table entry, which is the branch
//@ mechanism: this shape exercises and the trait-dispatch shapes do not.
//@ accept-means: a fn-pointer coercion launders the invariant premise — the same laundering
//@ accept-means: that once let a coerced callee credit a postcondition and owe nothing.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, returns 2, and claims 10.
//@ teeth: the direct-call twin callee_typeinv_precondition_free_grant_twofield MEASURED as
//@ teeth: ACCEPTED, exit 0, before the call-site obligation existed.
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
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    let f: fn(Sum10) -> i32 = total;
    f(s)
}
