//@ expect: reject
//@ also-verified: <Sum10 as Total>::total
//@ mechanism: the `Box` spelling of generic_struct_field_typeinv_uncharged: `via<T>(t: Box<T>)`.
//@ mechanism: The builder states a type parameter's invariant for a parameter typed `T`, `&T`,
//@ mechanism: `&mut T`, a tuple field or an enum payload, and nothing for a `T` one `Box` down, so
//@ mechanism: `via` holds nothing about `*t` and its hop `(*t).total()` owes an `inv_T` nothing
//@ mechanism: grants, while the call fixing `T = Sum10` owes nothing for the boxed value.
//@ accept-means: a type-parameter invariant behind a `Box` is neither granted nor owed, and the
//@ accept-means: caller that broke the boxed value is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED as a live false credit on the current build: `caller` is printed
//@ teeth: `verified`, and `via` is `unknown`: its goal `inv_T(*t)` is refuted with nothing
//@ teeth: granting it, a refutation of the opaque `inv_T` that is withheld. OPEN (D-141):
//@ teeth: committed RED, not declared, with the plain-struct class it belongs to — a concrete
//@ teeth: `Box<Sum10>` parameter is granted nothing either.
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

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: Box<T>) -> i32 {
    (*t).total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via(Box::new(s))
}
