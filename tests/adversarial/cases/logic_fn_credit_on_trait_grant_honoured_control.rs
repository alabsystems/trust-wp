//@ expect: verify
//@ mechanism: control for logic_fn_credit_on_trait_grant_refuted_by_impl.rs: the impl's `v` is `1`, so the grant is discharged and `T2::w`'s credit stands.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@ teeth: n/a — over-refusal control for withdrawing a logic credit with the trait grant it rests on.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait T1 {
    #[logic]
    #[ensures(result >= 0)]
    fn v(self) -> Int;
}

pub trait T2: T1 + Sized {
    #[logic]
    #[ensures(result >= 0)]
    fn w(self) -> Int {
        self.v()
    }
}

impl T1 for i32 {
    #[logic(open)]
    fn v(self) -> Int {
        pearlite! { 1 }
    }
}

impl T2 for i32 {}
