//@ expect: reject
//@ mechanism: the contracted trait method has a DEFAULT BODY, so it sits in the user spec
//@ mechanism: table as well as the trait one, and the user entry is the one call resolution
//@ mechanism: returns. `callee_invariant_requires` then answers from its first arm — the
//@ mechanism: callee's OWN table entry — whose invariant vector is empty because `Self` is a
//@ mechanism: type parameter in the trait. The body that actually runs is the overriding
//@ mechanism: impl's, and that one is verified holding `inv(self)`. Grant and obligation in
//@ mechanism: different code, one arm over from the trait-declaration lane.
//@ accept-means: resolving the body from the call's generic arguments is skipped whenever the
//@ accept-means: callee has a body of its own, so a default body re-opens the free grant for
//@ accept-means: every impl that overrides it.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, returns 2, and claims 10.
//@ teeth: MEASURED as ACCEPTED, exit 0, "3 verified, 0 failed". The companion
//@ teeth: trait_default_body_override_typeinv_baseline is the same program with the
//@ teeth: `Invariant` impl deleted, and there the impl method FAILS — which is what says the
//@ teeth: invariant premise is the only thing carrying the impl's proof.
//@ also-verified: Total::total, <Sum10 as Total>::total
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
