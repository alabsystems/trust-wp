//@ expect: reject
//@ mechanism: the contract lives on the TRAIT DECLARATION, so the call site reads it out of
//@ mechanism: the trait spec table. That table hardcodes an empty invariant-precondition
//@ mechanism: vector, while the impl body is verified from the user spec table WITH
//@ mechanism: `inv(self)` as a premise: the grant and the obligation are in different code.
//@ mechanism: `caller` holds `inv(s)` legitimately (its own parameter) and BREAKS it before
//@ mechanism: the call, so no lost ADT sort on a struct literal can be blamed for the verdict.
//@ accept-means: a contract on a trait declaration re-opens the free grant the free-function
//@ accept-means: lane closed: the impl reasons from an invariant no caller has to establish.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, returns 2, and claims 10.
//@ teeth: MEASURED as ACCEPTED, exit 0, "2 verified, 0 failed". The companion baseline
//@ teeth: `trait_decl_contract_without_invariant_baseline` is the same program with the
//@ teeth: `Invariant` impl deleted, and there the impl method FAILS — which is what says the
//@ teeth: invariant premise is the only thing carrying the impl's proof here.
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
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    s.total()
}
