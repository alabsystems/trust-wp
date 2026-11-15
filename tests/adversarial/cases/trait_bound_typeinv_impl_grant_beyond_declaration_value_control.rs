//@ expect: verify
//@ mechanism: the isolating twin of trait_bound_typeinv_impl_grant_beyond_declaration: the same
//@ mechanism: `caller` building the same `Seven` literal for the same hop, differing only in the
//@ mechanism: fields — 3 and 4, which keep `Seven`'s invariant, so the impl returns 10. The
//@ mechanism: call fixing `T = Seven` owes `Seven`'s invariant of the literal, unfolded at its
//@ mechanism: components (D-65, D-141); the pair is what says that obligation is real (D-68).
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

pub struct Seven {
    pub n: i32,
    pub m: i32,
}

impl Invariant for Seven {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.n@ + self.m@ == 7 }
    }
}

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self, s: Sum10) -> i32;
}

impl Total for Seven {
    #[ensures(result@ == 10)]
    fn total(self, s: Sum10) -> i32 {
        self.n + self.m + 3
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T, s: Sum10) -> i32 {
    t.total(s)
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    via(Seven { n: 3, m: 4 }, s)
}
