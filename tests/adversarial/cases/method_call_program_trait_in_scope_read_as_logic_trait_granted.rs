//@ expect: reject
//@ mechanism: the only trait in scope with an `m` for `S` is Tr1, whose `m` is a PROGRAM method (0);
//@ mechanism: the logic `<S as other::Tr2>::m` (10) belongs to a trait never imported here. Rust reads
//@ mechanism: `s.m()` as the program call; the resolver picks the only LOGIC member defined for `S`,
//@ mechanism: and `f`, which returns 10, is credited.
//@ fixed-by: D-196 — a method call's logic pick stands only where Rust's method lookup can select no
//@ fixed-by: other method of the name on any step of the receiver (`method_lookup::selects_only`).
//@ accept-means: `f` claims `result == s.m()` with Rust's `m` Tr1's program method (0), returns 10,
//@ accept-means: and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `unknown`: the pick is withheld and the encoder's dispatch refuses.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1 {
    fn m(self) -> u32;
}
impl Tr1 for S {
    fn m(self) -> u32 {
        0
    }
}

pub mod other {
    use super::*;
    pub trait Tr2 {
        #[logic]
        fn m(self) -> u32;
    }
    impl Tr2 for S {
        #[logic(open)]
        fn m(self) -> u32 {
            pearlite! { 10u32 }
        }
    }
}

#[ensures(result == s.m())]
pub fn f(s: S) -> u32 {
    10
}
