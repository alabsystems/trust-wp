//@ expect: verify
//@ xfail: `caller` is FAILED on a TRUE program, and the defect is the post-loop lane's, not the
//@ xfail: charge's: that lane does not bind a local built after the loop to its value, so ANY
//@ xfail: callee precondition over it is refuted with `s` arbitrary. A written `requires` over the
//@ xfail: same value is refuted identically, before D-141 too: post_loop_callee_requires_control.
//@ xfail: Uncharged, this twin was unknown (a sort-coercion bridge). Retire this directive when the
//@ xfail: post-loop lane binds a local to the value it was built as. At D-165 `caller` is
//@ xfail: `unknown (incomplete loop: no single post-loop return value)` first: the post-loop return
//@ xfail: walk gives `total(s)`'s result no value, so `result` is unbound and the refutation is withheld.
//@ mechanism: the value twin of post_loop_callee_typeinv_uncharged: 3 and 7 keep the invariant.
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
    let s = Sum10 { a: 3, b: 7 };
    total(s)
}
