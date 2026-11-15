//@ expect: reject
//@ also-verified: via
//@ mechanism: the refused generic hop of generic_hop_typeinv_box_type_argument, inside an annotated
//@ mechanism: loop body. `via(Box::new(s))` fixes `T = Box<Sum10>`, where the instantiation refuses
//@ mechanism: (D-141), and the per-loop obligation group owes the refusal as a fail-closed `false`.
//@ accept-means: a refused grant is dropped by the loop lane, and the caller that broke the boxed
//@ accept-means: value is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` builds a `Sum10` of 1 and 1 in the loop, the impl for
//@ WHY THE CONTRACT IS FALSE: `Box<Sum10>` returns 2 through `via`, and `caller` claims 10 whenever
//@ WHY THE CONTRACT IS FALSE: the loop runs.
//@ teeth: MEASURED on one build with the loop lanes' charge disabled by a local knob: `caller` is
//@ teeth: printed `verified`. Now `caller` is unknown and the impl is refuted on its own contract.
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
pub fn caller(n: u32) -> i32 {
    let mut r = 10;
    let mut i = 0;
    #[invariant(r@ == 10)]
    while i < n {
        let s = Sum10 { a: 1, b: 1 };
        r = via(Box::new(s));
        i += 1;
    }
    r
}
