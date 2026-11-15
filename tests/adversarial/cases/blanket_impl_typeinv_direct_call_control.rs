//@ expect: verify
//@ mechanism: the isolating twin of blanket_impl_typeinv_direct_call, differing only in the
//@ mechanism: values `caller` writes — 3 and 7, which keep `Sum10`'s invariant (D-141).
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

pub trait Inner {
    #[ensures(result@ == 10)]
    fn inner(self) -> i32;
}

impl Inner for Sum10 {
    fn inner(self) -> i32 {
        self.a + self.b
    }
}

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
}

impl<U: Inner> Total for U {
    #[ensures(result@ == 10)]
    fn total(self) -> i32 {
        self.inner()
    }
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 3;
    s.b = 7;
    s.total()
}
