//@ expect: reject
//@ also-verified: <Sum10 as Total>::total
//@ mechanism: a struct WITHOUT its own invariant holding an invariant-bearing field. Creusot's
//@ mechanism: `inv(Wrapper)` is structural — `inv(w.s)` — so `f` is granted it and `caller`
//@ mechanism: owes it. The parameter-clause builder states no structural invariant for a plain
//@ mechanism: struct, so `f` holds nothing about `w.s` and fails at the hop into the impl,
//@ mechanism: while `caller` owes nothing for the broken `Sum10` it wraps.
//@ accept-means: an invariant-bearing value hidden in a field of a plain struct reaches an impl
//@ accept-means: that reasons from `inv(self)`, and the caller that built it is credited.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED as a live false credit on the current build: `caller` is printed
//@ teeth: `verified`, `f` FAILS. OPEN (D-141): committed RED, not declared.
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

pub struct Wrapper {
    pub s: Sum10,
    pub k: i32,
}

#[ensures(result@ == 10)]
pub fn f(w: Wrapper) -> i32 {
    w.s.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    f(Wrapper { s, k: 0 })
}
