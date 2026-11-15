//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: <Sum10 as Total>::total
//@ mechanism: the type parameter as an enum payload: `via<T>(o: Option<T>)` holds
//@ mechanism: `match o { Some(x) => inv_T(x), None => true }`, and `via(Some(s))` owes the same
//@ mechanism: match with `Sum10`'s invariant in the arm, where it fixes `T` (D-141).
//@ accept-means: only a parameter typed by the type parameter itself is charged, so wrapping the
//@ accept-means: value in an `Option` launders it.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED with the instantiating call's clause dropped by a local knob: `caller` is
//@ teeth: credited `verified`. `via` is not credited either way: ay proves it and the strict
//@ teeth: certificate is withheld (proof-trusted), as for the concrete `Option<Sum10>` body.
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
pub fn via<T: Total>(o: Option<T>) -> i32 {
    match o {
        Some(t) => t.total(),
        None => 10,
    }
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via(Some(s))
}
