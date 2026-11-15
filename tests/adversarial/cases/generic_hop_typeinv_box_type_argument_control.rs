//@ expect: verify
//@ xfail: the price of refusing at a `Box`: 3 and 7 keep the invariant and the call that fixes
//@ xfail: `T = Box<Sum10>` is refused all the same (D-141), and the impl, granted nothing at a
//@ xfail: `Box`, is refuted on its own contract, as it was before D-141. Retire this directive when
//@ xfail: the builder states `inv(*b)` for a `Box` parameter and the instantiation reads it.
//@ mechanism: the value twin of generic_hop_typeinv_box_type_argument.
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

impl Total for Box<Sum10> {
    fn total(self) -> i32 {
        self.a + self.b
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
    via(Box::new(s))
}
