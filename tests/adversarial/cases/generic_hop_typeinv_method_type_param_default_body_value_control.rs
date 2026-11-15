//@ expect: verify
//@ mechanism: the value twin of generic_hop_typeinv_method_type_param_default_body: 3 and 7 keep
//@ mechanism: `Sum10`'s invariant, so the charge at the call that fixes the type parameter is paid
//@ mechanism: and every function verifies. The pair differs in the value alone (D-68).
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

pub trait Hop {
    #[ensures(result@ == 10)]
    fn hop<T: Total>(&self, t: T) -> i32 {
        t.total()
    }
}

pub struct H;
impl Hop for H {}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 3;
    s.b = 7;
    H.hop(s)
}
