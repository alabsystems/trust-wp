//@ expect: reject
//@ mechanism: teeth witness for trait_default_body_override_typeinv_free_grant: the identical
//@ mechanism: program with the `Invariant` impl deleted. Nothing else changes, so a rejection
//@ mechanism: here is what proves the free grant — not the trait contract and not the
//@ mechanism: refinement check — is what carries the twin.
//@ accept-means: the twin's accept would have some other cause than the invariant premise.
//@ WHY THE CONTRACT IS FALSE: `<Sum10 as Total>::total` returns `a + b`, which without an
//@ WHY THE CONTRACT IS FALSE: invariant is unconstrained, and the inherited ensures claims 10.
//@ teeth: MEASURED rejected with the impl method FAILED while the twin is ACCEPTED.
//@ also-verified: Total::total, caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
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
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    s.total()
}
