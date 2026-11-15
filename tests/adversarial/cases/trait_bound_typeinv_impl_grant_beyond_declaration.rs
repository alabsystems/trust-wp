//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, <Seven as Total>::total
//@ mechanism: the impl's `Self` is an invariant-bearing ADT where the trait declaration has a
//@ mechanism: type parameter, so the impl is granted `inv(self)` at a position the declaration
//@ mechanism: types generically. `via<T: Total>` holds `inv_T(t)` and owes it at `t.total(s)`;
//@ mechanism: the declaration's `Self` clause, stated at the impl, is `Seven`'s invariant, so it
//@ mechanism: covers the grant; and the call that FIXES `T = Seven` owes `Seven`'s invariant of
//@ mechanism: the value it hands over (D-141).
//@ accept-means: a call that instantiates a generic parameter owes nothing for it, so one
//@ accept-means: generic hop hands every Self-typed invariant away free.
//@ WHY THE CONTRACT IS FALSE: `caller` hands `via` a `Seven` whose fields are 0 and 0, so the
//@ WHY THE CONTRACT IS FALSE: impl returns 3 while `Total::total` claims 10.
//@ teeth: MEASURED on one build with the instantiating call's clause dropped by a local knob:
//@ teeth: `caller` is credited `verified`, exit 0. `via` is verified either way, and TRUE: it
//@ teeth: holds `inv_T(t)`, the precondition Creusot gives every parameter.
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

pub struct Seven {
    pub n: i32,
    pub m: i32,
}

impl Invariant for Seven {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.n@ + self.m@ == 7 }
    }
}

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self, s: Sum10) -> i32;
}

impl Total for Seven {
    #[ensures(result@ == 10)]
    fn total(self, s: Sum10) -> i32 {
        self.n + self.m + 3
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T, s: Sum10) -> i32 {
    t.total(s)
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    via(Seven { n: 0, m: 0 }, s)
}
