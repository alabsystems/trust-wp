//@ expect: reject
//@ also-verified: caller, <Sum10 as Total>::total
//@ mechanism: the generic spelling of std_into_blanket_to_local_from_typeinv_uncharged.rs.
//@ mechanism: `impl<T: Total> From<T> for Out` is reached through std's blanket `Into`: the call in
//@ mechanism: `caller` enters std's `into`, and std's body calls `from` with the value unexamined, so
//@ mechanism: no route into `from` can owe a premise. A local impl of a FOREIGN trait's method is
//@ mechanism: therefore granted none (`implements_foreign_trait_method`): `from`'s hop into the impl
//@ mechanism: owes `inv_T(t)`, nothing establishes it, and `from` is refused. `caller` is credited
//@ mechanism: TRUE: with nothing granted, its call through std owes nothing, and `from` is the
//@ mechanism: function whose body breaks its contract. Before the foreign impl lost its premise,
//@ mechanism: `from` was credited on `inv_T(t)` and the crate exited 0.
//@ accept-means: a crate reported verified panics inside a trait impl it credits as panic-free,
//@ accept-means: called by std's blanket `Into` with a value that breaks the invariant `T` was granted.
//@ WHY THE PROGRAM IS WRONG: `into()` hands `from` a `Sum10` with `a + b == 2`, the impl returns 2,
//@ WHY THE PROGRAM IS WRONG: and `100 / (r - 2)` in `from` divides by zero.
//@ fixed-by: D-141 — an impl of a foreign trait's method holds no parameter premise.
//@ teeth: MEASURED on one build with foreign impls granted again by a knob: ACCEPTED, exit 0, `from`
//@ teeth: and `caller` verified; with the rule, `from` unknown. REJECTED on the build before the
//@ teeth: type-parameter grant (`from` refused at its hop, D-75).
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

pub struct Out {
    pub v: i32,
}

impl<T: Total> From<T> for Out {
    #[ensures(true)]
    fn from(t: T) -> Out {
        let r = t.total();
        Out { v: 100 / (r - 2) }
    }
}

#[ensures(true)]
pub fn caller() -> i32 {
    let o: Out = Sum10 { a: 1, b: 1 }.into();
    o.v
}
