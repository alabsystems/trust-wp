//@ expect: verify
//@ mechanism: the TRUE twin of trait_decl_contract_typeinv_free_grant: the same trait, the
//@ mechanism: same impl, the same claim, and a receiver that SATISFIES the invariant because
//@ mechanism: the caller forwards its own parameter untouched. It is what says whether the
//@ mechanism: reject twin rejects because the invariant is broken or because the trait lane
//@ mechanism: refuses every receiver.
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
    fn total(self) -> i32;
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    s.total()
}
