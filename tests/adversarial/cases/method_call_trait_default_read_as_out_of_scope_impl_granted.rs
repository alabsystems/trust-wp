//@ expect: reject
//@ mechanism: method syntax `s.m()` is resolved by Rust's method lookup: among the traits IN SCOPE at
//@ mechanism: the clause. Only Tr1 is (Tr2 is declared in `other` and never imported), and `S`
//@ mechanism: takes Tr1's default body (10). The resolver types the receiver and picks the only impl
//@ mechanism: member defined for `S` (`identity_typed::resolve_family_on_type`): `<S as
//@ mechanism: other::Tr2>::m` (0), an impl of a trait Rust never consults here, while the default
//@ mechanism: that Rust does select is not a candidate. `f`, which returns 0, is credited.
//@ fixed-by: D-196 — a method call's logic pick stands only where Rust's method lookup can select no
//@ fixed-by: other method of the name on any step of the receiver (`method_lookup::selects_only`).
//@ accept-means: `f` claims `result == s.m()` (10), returns 0, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `unknown`: the pick is withheld and the encoder's dispatch refuses (`Rust's
//@ teeth: method lookup on that receiver may select another method named `m``).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1 {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}
impl Tr1 for S {}

pub mod other {
    use super::*;
    pub trait Tr2 {
        #[logic]
        fn m(self) -> u32;
    }
    impl Tr2 for S {
        #[logic(open)]
        fn m(self) -> u32 {
            pearlite! { 0u32 }
        }
    }
}

#[ensures(result == s.m())]
pub fn f(s: S) -> u32 {
    0
}
