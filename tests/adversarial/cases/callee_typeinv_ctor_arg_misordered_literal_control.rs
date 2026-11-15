//@ expect: verify
//@ mechanism: the TRUE twin of callee_typeinv_ctor_arg_misordered_literal. Same
//@ mechanism: out-of-declaration-order literal, values exchanged so the invariant holds. The
//@ mechanism: pair is what says the unfold reads DECLARED indices rather than refusing every
//@ mechanism: misordered literal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct OnlyA {
    pub a: i32,
    pub b: i32,
}

impl Invariant for OnlyA {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ == 1 }
    }
}

#[ensures(result@ == 1)]
pub fn takes(s: OnlyA) -> i32 {
    s.a
}

#[ensures(result@ == 1)]
pub fn caller() -> i32 {
    takes(OnlyA { b: 9, a: 1 })
}
