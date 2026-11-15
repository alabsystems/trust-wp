//@ expect: verify
//@ mechanism: the let-bound twin of the inline-literal shape, so the next reader does not
//@ mechanism: have to re-measure whether the binding is what matters: it is not, and both
//@ mechanism: spellings reach the unfold. Its RED twin is
//@ mechanism: callee_typeinv_constructed_arg_broken_letbound.
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
    let v = Sum10 { a: 4, b: 6 };
    total(v)
}
