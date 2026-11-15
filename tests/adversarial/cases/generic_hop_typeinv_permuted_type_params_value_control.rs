//@ expect: verify
//@ mechanism: the value twin of generic_hop_typeinv_permuted_type_params: 3 and 7 keep `Sum10`'s
//@ mechanism: invariant, so the charge at the call that fixes the type parameter is paid and every
//@ mechanism: function verifies. The pair differs in the value alone (D-68).
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
pub fn via<A, B: Total>(_a: A, b: B) -> i32 {
    b.total()
}

#[ensures(result@ == 10)]
pub fn mid<B: Total, A>(b: B, a: A) -> i32 {
    via(a, b)
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 3;
    s.b = 7;
    mid(s, 0u8)
}
