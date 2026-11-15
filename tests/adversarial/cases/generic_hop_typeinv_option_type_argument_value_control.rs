//@ expect: verify
//@ xfail: two defects that predate D-141 and are unchanged by it, measured before it too: the
//@ xfail: impl for `Option<Sum10>` is refuted by its TRAIT REFINEMENT check (its premise is
//@ xfail: the builder's match, which the refinement lane does not find in the declaration),
//@ xfail: and `via` is refused by the covering check, which cannot read a match. `caller`
//@ xfail: itself verifies here and is refuted in the RED twin: the pair isolates the charge.
//@ xfail: Retire this directive when refinement and covering both read a decomposed premise.
//@ mechanism: the value twin of generic_hop_typeinv_option_type_argument: 3 and 7 keep the invariant.
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

impl Total for Option<Sum10> {
    fn total(self) -> i32 {
        match self {
            Some(s) => s.a + s.b,
            None => 10,
        }
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
    via(Some(s))
}
