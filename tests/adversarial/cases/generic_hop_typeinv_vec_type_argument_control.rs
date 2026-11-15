//@ expect: verify
//@ xfail: the price of refusing at a sequence container: 3 and 7 keep the invariant and the
//@ xfail: call that fixes `T = Vec<Sum10>` is refused all the same, since no clause the builder
//@ xfail: states names the element invariant of THIS instantiation (D-141). The impl's own read
//@ xfail: of `self[0]` is refuted as well, as it was before D-141. Retire this directive when the
//@ xfail: element bridge is keyed on the element type.
//@ mechanism: the value twin of generic_hop_typeinv_vec_type_argument.
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

impl Total for Vec<Sum10> {
    fn total(self) -> i32 {
        if self.len() == 0 {
            10
        } else {
            self[0].a + self[0].b
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
    let mut v = Vec::new();
    v.push(s);
    via(v)
}
