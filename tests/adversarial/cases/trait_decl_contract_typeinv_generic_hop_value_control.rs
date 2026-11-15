//@ expect: verify
//@ mechanism: the isolating twin of trait_decl_contract_typeinv_generic_hop: the same program,
//@ mechanism: the same overwrite of `s` before the same generic hop, differing only in the
//@ mechanism: values written — 3 and 7, which keep `Sum10`'s invariant. The call fixing
//@ mechanism: `T = Sum10` owes `inv(s)` for the value `caller` built (D-141), so this pair is
//@ mechanism: what says the obligation is real rather than a refusal of the hop (D-68).
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
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 3;
    s.b = 7;
    via(s)
}
