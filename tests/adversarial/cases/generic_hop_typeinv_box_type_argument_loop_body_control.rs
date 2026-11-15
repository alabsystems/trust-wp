//@ expect: verify
//@ xfail: the price of refusing at a `Box` (D-141), inside an annotated loop body: 3 and 7 keep the
//@ xfail: invariant and `caller` is refused all the same. Retire this directive when the builder
//@ xfail: states `inv(*b)` for a `Box` parameter and the instantiation reads it.
//@ xfail-verdict: unknown
//@ mechanism: the value twin of generic_hop_typeinv_box_type_argument_loop_body, with an impl that
//@ mechanism: verifies. The refusal is a fail-closed `false` the loop lane owes UNGUARDED, where the
//@ mechanism: verdict gate reads it as the marker it is: behind the loop's path guard, any model of
//@ mechanism: the guard refuted it, and `caller` was printed FAILED with a counterexample on this
//@ mechanism: TRUE program.
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
        10
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(n: u32) -> i32 {
    let mut r = 10;
    let mut i = 0;
    #[invariant(r@ == 10)]
    while i < n {
        let s = Sum10 { a: 3, b: 7 };
        r = via(Box::new(s));
        i += 1;
    }
    r
}
