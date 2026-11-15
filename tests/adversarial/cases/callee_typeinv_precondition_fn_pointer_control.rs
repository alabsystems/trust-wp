//@ expect: verify
//@ mechanism: the TRUE twin of callee_typeinv_precondition_fn_pointer — the same coercion with
//@ mechanism: a value that satisfies the invariant. It says the fn-pointer route still states
//@ mechanism: a dischargeable obligation rather than refusing the coercion outright.
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
pub fn caller(s: Sum10) -> i32 {
    let f: fn(Sum10) -> i32 = total;
    f(s)
}
