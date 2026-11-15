//@ expect: reject
//@ verdict: failed
//@ fn-failed: <Sum10 as Total>::total
//@ mechanism: trait_decl_contract_typeinv_free_grant with the `Invariant` impl DELETED. The
//@ mechanism: impl method then has nothing to prove `result@ == 10` from and must fail. It is
//@ mechanism: the witness that the invariant premise — not the trait contract, not the
//@ mechanism: refinement check — is what carries the impl's proof in the twin.
//@ accept-means: a trait impl can prove an arbitrary inherited postcondition with no premise
//@ accept-means: at all, which would make the twin's verdict say nothing about invariants.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, returns 2, and claims 10;
//@ WHY THE CONTRACT IS FALSE: `total` claims 10 for every `Sum10`.
//@ teeth: MEASURED as `failed` on the same build where the twin measures ACCEPTED.
//@ also-verified: caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
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
