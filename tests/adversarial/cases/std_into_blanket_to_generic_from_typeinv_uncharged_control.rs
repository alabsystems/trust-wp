//@ expect: verify
//@ xfail: D-141's price: an impl of a foreign trait's method holds no parameter premise, since std
//@ xfail: reaches it from code no lane walks, so `from`'s hop owes `inv_T(t)` with nothing to
//@ xfail: establish it (`from unknown (refutation withheld: the violated goal is a type parameter's
//@ xfail: invariant ...)`). Creusot charges `inv` at every call, std's included.
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of std_into_blanket_to_generic_from_typeinv_uncharged.rs: the value
//@ mechanism: converted keeps its invariant.
//@ teeth: control — refused before the type-parameter grant (D-75), verified while the impl held a
//@ teeth: premise no route owed, refused once it holds none.
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
    let o: Out = Sum10 { a: 3, b: 7 }.into();
    o.v
}
