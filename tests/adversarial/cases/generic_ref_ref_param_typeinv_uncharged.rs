//@ expect: reject
//@ also-verified: <Sum10 as Total>::total
//@ mechanism: a type parameter two references down: `via<T>(t: &&T)`. The builder states a type
//@ mechanism: parameter's invariant behind ONE reference (`inv_T(t)` for `&T`, `inv_T(*t)` for
//@ mechanism: `&mut T`) and nothing behind a second, so `via` holds nothing about `**t` and its hop
//@ mechanism: `(**t).total()` owes an `inv_T` nothing grants, while the call fixing `T = Sum10`
//@ mechanism: owes nothing for the referent.
//@ accept-means: a type-parameter invariant behind a second reference is neither granted nor
//@ accept-means: owed, and the caller that broke the referent is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED as a live false credit on the current build: `caller` is printed
//@ teeth: `verified`, and `via` is `unknown`: its goal `inv_T` of the referent is refuted with
//@ teeth: nothing granting it, a refutation of the opaque `inv_T` that is withheld. OPEN (D-141):
//@ teeth: committed RED, not declared, with the plain-struct class it belongs to.
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
    fn total(&self) -> i32;
}

impl Total for Sum10 {
    fn total(&self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: &&T) -> i32 {
    (**t).total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    let r = &s;
    via(&r)
}
