//@ expect: verify
//@ mechanism: the TRUE twin of trait_decl_contract_typeinv_generic_hop — the same hop with a
//@ mechanism: receiver that satisfies the invariant because it is the caller's own parameter.
//@ mechanism: The call fixing `T = Sum10` owes `inv(s)` and discharges it from the caller's
//@ mechanism: premise (D-141). `..._value_control` is the twin differing in the value alone.
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
pub fn via<T: Total>(t: T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    via(s)
}
