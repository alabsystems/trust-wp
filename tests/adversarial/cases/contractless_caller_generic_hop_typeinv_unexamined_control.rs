//@ expect: verify
//@ xfail: D-141's price. `hop`, now a target, is contract-free, so its credit rests on D-104's panic
//@ xfail: account, which reads a generic body at no instantiation: `hop unknown (partial: panic paths
//@ xfail: unchecked (call to via (unchecked panic paths in via)))`. The same `hop` with a written
//@ xfail: contract verifies (trait_decl_contract_typeinv_generic_hop_value_control.rs is that shape).
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of contractless_caller_generic_hop_typeinv_unexamined.rs: `hop` hands
//@ mechanism: `via` a `Sum10` whose invariant holds.
//@ teeth: control — refused before D-141 (`via` at its hop, D-75), verified while `hop` was examined
//@ teeth: by nothing, refused once it is a target.
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
    let r = t.total();
    100 / (r - 2) + 10 - 100 / (r - 2)
}

pub fn hop() -> i32 {
    via(Sum10 { a: 3, b: 7 })
}
