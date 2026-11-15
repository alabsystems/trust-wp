//@ expect: verify
//@ mechanism: the invariant is TAUTOLOGICAL and the struct has two fields, so neither the
//@ mechanism: invariant's content nor a newtype collapse can be what decides the verdict:
//@ mechanism: the caller-constructed aggregate alone does. It measured the WIDTH of the
//@ mechanism: over-refusal while the obligation could be discharged only from a premise the
//@ mechanism: caller already held; it now pins the floor of the unfold — an aggregate the
//@ mechanism: caller built is decidable even when the body says nothing at all.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct T2 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for T2 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ == self.a@ }
    }
}

#[ensures(result@ == 1)]
pub fn one(s: T2) -> i32 {
    let _ = s;
    1
}

#[ensures(result@ == 1)]
pub fn caller() -> i32 {
    one(T2 { a: 7, b: 8 })
}
