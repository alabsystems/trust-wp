//@ expect: verify
//@ mechanism: the missing half of the D-62 trait-table evidence: the isolating twin of
//@ mechanism: callee_typeinv_free_grant_trait_method. That case's own control passes the
//@ mechanism: CALLER'S OWN PARAMETER, which discharges by matching a premise the caller
//@ mechanism: already holds — a different route, so it cannot tell a real obligation from a
//@ mechanism: blanket refusal of constructed arguments. This one differs from the RED case in
//@ mechanism: the constructed VALUE alone.
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
    fn total(&self, s: Sum10) -> i32;
}

pub struct T0;

impl Total for T0 {
    #[ensures(result@ == 10)]
    fn total(&self, s: Sum10) -> i32 {
        s.a + s.b
    }
}

#[ensures(result@ == 10)]
pub fn caller<T: Total>(t: T) -> i32 {
    t.total(Sum10 { a: 4, b: 6 })
}
