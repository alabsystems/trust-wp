//@ expect: reject
//@ mechanism: the struct-literal twin of trait_decl_contract_typeinv_free_grant. In the
//@ mechanism: free-function lane an inline literal argument only ever produces an
//@ mechanism: over-refusal, because the obligation lands on an uninterpreted symbol; in the
//@ mechanism: trait-declaration lane no obligation is stated at all, so the literal verifies.
//@ accept-means: the same free grant, reached by the shape the free-function lane refuses.
//@ WHY THE CONTRACT IS FALSE: `caller` builds `Sum10 { a: 1, b: 1 }`, returns 2, claims 10.
//@ teeth: MEASURED as ACCEPTED, exit 0, "2 verified, 0 failed".
//@ also-verified: <Sum10 as Total>::total
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
pub fn caller() -> i32 {
    Sum10 { a: 1, b: 1 }.total()
}
