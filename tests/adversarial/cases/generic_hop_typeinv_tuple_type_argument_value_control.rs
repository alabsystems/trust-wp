//@ expect: verify
//@ xfail: two defects that predate D-141 and are unchanged by it, measured before it too: the
//@ xfail: impl for `(Sum10, i32)` is refuted by its TRAIT REFINEMENT check (its premise is a
//@ xfail: field clause the refinement lane does not find in the declaration), and `via` is
//@ xfail: refused by the covering check, which cannot place a field clause. `caller` itself
//@ xfail: verifies here and is refuted in the RED twin: the pair isolates the charge. Retire
//@ xfail: this directive when refinement and covering both read a decomposed premise.
//@ mechanism: the value twin of generic_hop_typeinv_tuple_type_argument: 3 and 7 keep the invariant.
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

impl Total for (Sum10, i32) {
    fn total(self) -> i32 {
        self.0.total()
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
    via((s, 0))
}
