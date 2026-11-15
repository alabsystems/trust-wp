//@ expect: verify
//@ mechanism: the TRUE twin of callee_typeinv_free_grant_trait_method: the same trait
//@ mechanism: dispatch, with the caller's OWN parameter as the argument so the invariant
//@ mechanism: the trait declaration now owes is one the caller already holds. It is what
//@ mechanism: says the reject twin rejects for the broken value and not because a trait
//@ mechanism: call can no longer discharge the obligation at all.
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

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(&self, s: Sum10) -> i32;
}

pub struct T0;

impl Total for T0 {
    #[ensures(result@ == 10)]
    fn total(&self, s: Sum10) -> i32 {
        s.a + s.b
    }
}

#[ensures(result@ == 10)]
pub fn caller<T: Total>(t: T, s: Sum10) -> i32 {
    t.total(s)
}
