//@ expect: reject
//@ also-verified: <Sum10 as Total>::total
//@ mechanism: the generic spelling of struct_field_typeinv_uncharged: `via<T>(w: Pair<T>)` over a
//@ mechanism: plain generic struct. The builder states no structural invariant for a plain
//@ mechanism: struct, concrete or generic, so `via` holds nothing about `w.t` and fails at
//@ mechanism: `w.t.total()`, while the call fixing `T = Sum10` owes nothing for the field.
//@ accept-means: a type-parameter invariant one struct field down is neither granted nor owed.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED as a live false credit on the current build: `caller` is printed
//@ teeth: `verified`, and `via` is not credited: its goal `inv_T(w.t)` is refuted with nothing
//@ teeth: granting it, a refutation of the opaque `inv_T` that is withheld as `unknown`. OPEN
//@ teeth: (D-141): committed RED, not declared. Closing it for the generic spelling alone would
//@ teeth: leave the concrete one open for the same missing pass.
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

pub struct Pair<T> {
    pub t: T,
    pub k: i32,
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(w: Pair<T>) -> i32 {
    w.t.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    via(Pair { t: s, k: 0 })
}
