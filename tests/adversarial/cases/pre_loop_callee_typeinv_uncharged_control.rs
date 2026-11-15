//@ expect: verify
//@ xfail: the price of the pre-loop charge, measured: `caller` is unknown (timeout). It verified
//@ xfail: uncharged only because the obligation was not charged. The block collector writes the
//@ xfail: aggregate as the named constructor `Sum10(3, 7)`, which the D-65 unfold does not read,
//@ xfail: and the call's postcondition is scoped under that obligation, so the function-level goal
//@ xfail: rests on the solver deciding `inv(Sum10(3, 7))`. Retire this directive when every lane
//@ xfail: spells a built aggregate the way the unfold reads it.
//@ mechanism: the value twin of pre_loop_callee_typeinv_uncharged: 3 and 7 keep the invariant.
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
    let s = Sum10 { a: 3, b: 7 };
    let r = total(s);
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    r
}
