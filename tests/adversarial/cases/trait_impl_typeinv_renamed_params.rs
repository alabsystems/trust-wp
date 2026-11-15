//@ expect: reject
//@ verdict: failed
//@ mechanism: the impl names its parameters in the opposite order to the trait declaration,
//@ mechanism: so the clause vector the impl body was granted (`inv` on the parameter IT
//@ mechanism: calls `k`) and the name list a call site resolves from the declaration (where
//@ mechanism: `k` is the second parameter, an `i32`) disagree about which argument a name
//@ mechanism: denotes. A grant substituted against the other body's names states the
//@ mechanism: invariant about a value that never had it.
//@ accept-means: the clauses and the names they are written over are being read out of
//@ accept-means: different bodies, so the obligation lands on whichever argument shares a
//@ accept-means: parameter name — which at best refuses and at worst charges the wrong value.
//@ WHY THE CONTRACT IS FALSE: `caller` builds `Sum10 { a: 1, b: 1 }`, whose fields sum to 2,
//@ WHY THE CONTRACT IS FALSE: and the inherited ensures claims 10.
//@ teeth: MEASURED at the parent commit as a rejection whose CONTROL was also over-refused —
//@ teeth: the obligation landed on the `i32` and was undischargeable for every argument. The
//@ teeth: control verifying is what says the obligation now reaches the `Sum10`.
//@ also-verified: <T0 as Total>::total
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
pub fn caller() -> i32 {
    let t = T0;
    t.total(Sum10 { a: 1, b: 1 }, 7)
}
