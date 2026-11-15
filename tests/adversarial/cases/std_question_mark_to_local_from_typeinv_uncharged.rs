//@ expect: reject
//@ fn-failed: <Out as std::convert::From<Sum10>>::from
//@ also-verified: caller
//@ mechanism: the `?` spelling of std_into_blanket_to_local_from_typeinv_uncharged.rs: `e?` on an
//@ mechanism: `Err(Sum10 { .. })` in a function returning `Result<_, Out>` converts the error through
//@ mechanism: `From::from`, called by std's `FromResidual` with the value unexamined. A local impl of a
//@ mechanism: FOREIGN trait's method holds no parameter premise (`implements_foreign_trait_method`), so
//@ mechanism: `from`, which divides by a value only the invariant bounds, is refuted, and `caller`,
//@ mechanism: whose route through std owes nothing, is credited TRUE.
//@ accept-means: a crate reported verified panics inside a trait impl it credits as panic-free,
//@ accept-means: called by std's `?` with a value that breaks the invariant the impl was granted.
//@ WHY THE PROGRAM IS WRONG: `e?` hands `from` a `Sum10` with `a + b == 2`, and `100 / (r - 2)` in `from`
//@ WHY THE PROGRAM IS WRONG: divides by zero.
//@ fixed-by: D-141 — an impl of a foreign trait's method holds no parameter premise.
//@ teeth: MEASURED on one build with the three route arms knobbed off: ACCEPTED, exit 0, `from` and
//@ teeth: `caller` verified; with them, `from` FAILED.
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

pub struct Out {
    pub v: i32,
}

impl From<Sum10> for Out {
    fn from(s: Sum10) -> Out {
        let r = s.a + s.b;
        Out { v: 100 / (r - 2) }
    }
}

#[ensures(true)]
pub fn caller() -> Result<i32, Out> {
    let e: Result<i32, Sum10> = Err(Sum10 { a: 1, b: 1 });
    let v = e?;
    Ok(v)
}
