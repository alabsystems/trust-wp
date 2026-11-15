//@ expect: reject
//@ also-verified: via
//@ mechanism: the refused generic hop of generic_hop_typeinv_box_type_argument, inside a loop with
//@ mechanism: NO invariant. `via(Box::new(s))` fixes `T = Box<Sum10>`, where the instantiation
//@ mechanism: refuses (D-141), and the unannotated-loop walker owes the refusal as a fail-closed
//@ mechanism: `false`.
//@ accept-means: a refused grant is dropped by the unannotated-loop walker, and the caller that
//@ accept-means: broke the boxed value is credited.
//@ WHY THE CONTRACT IS FALSE: the call hands `via` a `Box` of a `Sum10` of 1 and 1, which breaks
//@ WHY THE CONTRACT IS FALSE: the invariant Creusot's `inv(Box<T>) = inv(*b)` makes the call owe: the
//@ WHY THE CONTRACT IS FALSE: call's precondition does not hold, and the impl it reaches returns 2
//@ WHY THE CONTRACT IS FALSE: where the trait promises 10.
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
    let mut i = 0;
    while i < n {
        let s = Sum10 { a: 1, b: 1 };
        let _r = via(Box::new(s));
        i += 1;
    }
    10
}
