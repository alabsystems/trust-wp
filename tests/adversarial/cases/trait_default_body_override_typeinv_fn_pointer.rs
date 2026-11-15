//@ expect: reject
//@ mechanism: the same free grant reached through a reified fn pointer. The call operand is a
//@ mechanism: local, so a resolver that reads only the operand constant names no body and the
//@ mechanism: first arm answers instead from the default-bodied trait method's own empty
//@ mechanism: vector. The local holds exactly one constant, so the overriding impl IS
//@ mechanism: determinable — the grant was skipped, not unavailable.
//@ accept-means: the fn-pointer route into an overridden default body owes nothing.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, returns 2, and claims 10.
//@ teeth: MEASURED as ACCEPTED, exit 0. The bodyless-declaration fn-pointer sibling
//@ teeth: (callee_typeinv_precondition_fn_pointer) is rejected.
//@ also-verified: Total::total, <Sum10 as Total>::total
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

pub trait Total: Sized {
    #[ensures(result@ == 10)]
    fn total(self) -> i32 {
        10
    }
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    let f: fn(Sum10) -> i32 = <Sum10 as Total>::total;
    s.a = 1;
    s.b = 1;
    f(s)
}
