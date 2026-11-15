//@ expect: verify
//@ mechanism: the TRUE twin of trait_bound_typeinv_impl_grant_beyond_declaration — the same
//@ mechanism: hop with a receiver forwarded from the caller's own parameter, whose invariant the
//@ mechanism: caller holds. `via` charges `inv_T(t)` at `t.total(s)` from its own premise, and
//@ mechanism: the call fixing `T = Seven` owes `Seven`'s invariant of `t`, discharged by that
//@ mechanism: premise (D-141). `..._value_control` is the twin differing in the value alone.
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
pub fn caller(t: Seven, s: Sum10) -> i32 {
    via(t, s)
}
