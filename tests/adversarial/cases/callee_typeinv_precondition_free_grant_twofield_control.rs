//@ expect: verify
//@ mechanism: the TRUE twin of callee_typeinv_precondition_free_grant_twofield: the same
//@ mechanism: callee, the same claim, and an argument that SATISFIES `a + b == 10`. It is
//@ mechanism: what says whether the reject twin rejects because the invariant is broken or
//@ mechanism: because the obligation is unprovable for every argument. It carried an xfail
//@ mechanism: for as long as a call-site invariant obligation could be discharged only from
//@ mechanism: a premise the caller already held; unfolding the invariant's defining body at
//@ mechanism: an aggregate the caller BUILT retires it.
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
    total(Sum10 { a: 4, b: 6 })
}
