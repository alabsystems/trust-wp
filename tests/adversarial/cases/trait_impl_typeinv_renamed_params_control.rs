//@ expect: verify
//@ mechanism: the TRUE twin of trait_impl_typeinv_renamed_params: the same renamed impl, with
//@ mechanism: the caller's own parameter as the invariant-bearing argument. It is what says
//@ mechanism: the obligation is stated about the `Sum10` the impl was granted `inv` of, and
//@ mechanism: not about whichever argument happens to share a parameter name.
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

pub struct T0;

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(&self, s: Sum10, k: i32) -> i32;
}

impl Total for T0 {
    #[ensures(result@ == 10)]
    fn total(&self, k: Sum10, s: i32) -> i32 {
        k.a + k.b
    }
}

#[ensures(result@ == 10)]
pub fn caller(v: Sum10) -> i32 {
    let t = T0;
    t.total(v, 7)
}
