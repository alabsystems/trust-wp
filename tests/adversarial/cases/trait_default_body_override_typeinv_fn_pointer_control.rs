//@ expect: verify
//@ mechanism: the TRUE twin of trait_default_body_override_typeinv_fn_pointer: the same
//@ mechanism: reified fn pointer into the same overriding impl, with a receiver that
//@ mechanism: SATISFIES the invariant because the caller forwards its own parameter
//@ mechanism: untouched. It is what says the fn-pointer route states a DISCHARGEABLE
//@ mechanism: obligation — that following the pointer to the body it can only enter charges
//@ mechanism: the grant rather than refusing every coercion.
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
pub fn caller(s: Sum10) -> i32 {
    let f: fn(Sum10) -> i32 = <Sum10 as Total>::total;
    f(s)
}
