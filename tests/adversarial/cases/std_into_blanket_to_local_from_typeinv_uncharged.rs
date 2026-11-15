//@ expect: reject
//@ fn-failed: <Out as std::convert::From<Sum10>>::from
//@ also-verified: caller
//@ mechanism: a local `impl From<Sum10> for Out` is reached through std's blanket
//@ mechanism: `impl<T, U: From<T>> Into<U> for T`: the call in `caller` enters std's `into`, and std's
//@ mechanism: body calls `from` with the value unexamined, so no route into `from` can owe a
//@ mechanism: premise. A local impl of a FOREIGN trait's method is therefore granted none
//@ mechanism: (`implements_foreign_trait_method`), and `from`, which divides by a value only the
//@ mechanism: invariant bounds, is refuted. `caller` is credited TRUE: with nothing granted, its call
//@ mechanism: through std owes nothing, and `from` is the function whose body breaks its contract.
//@ mechanism: The `?` spelling is std_question_mark_to_local_from_typeinv_uncharged.rs.
//@ accept-means: a crate reported verified panics inside a trait impl it credits as panic-free,
//@ accept-means: called by std's blanket `Into` with a value that breaks the invariant the impl was
//@ accept-means: granted.
//@ WHY THE PROGRAM IS WRONG: `into()` hands `from` a `Sum10` with `a + b == 2`, and `100 / (r - 2)`
//@ WHY THE PROGRAM IS WRONG: in `from` divides by zero.
//@ fixed-by: D-141 — an impl of a foreign trait's method holds no parameter premise.
//@ teeth: MEASURED on one build with foreign impls granted again by a knob: ACCEPTED, exit 0, `from`
//@ teeth: and `caller` verified; with the rule, `from` FAILED. ACCEPTED on the build before D-141 too.
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
pub fn caller() -> i32 {
    let o: Out = Sum10 { a: 1, b: 1 }.into();
    o.v
}
