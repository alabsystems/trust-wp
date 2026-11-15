//@ expect: reject
//@ mechanism: `S` has an inherent PROGRAM method `m` (0) and a logic trait method `<S as Tr>::m`
//@ mechanism: (10). Rust's method lookup takes the inherent method first, so `s.m()` is a program call
//@ mechanism: Pearlite refuses. The resolver only knows the logic definitions, finds one for `S` and
//@ mechanism: reads `s.m()` as `<S as Tr>::m`: `f`, which returns 10, is credited against a
//@ mechanism: contract whose `s.m()` Rust evaluates to 0.
//@ fixed-by: D-196 — a method call's logic pick stands only where Rust's method lookup can select no
//@ fixed-by: other method of the name on any step of the receiver (`method_lookup::selects_only`).
//@ accept-means: `f` claims `result == s.m()` with Rust's `m` the inherent program method (0),
//@ accept-means: returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `unknown`: the pick is withheld and the encoder's dispatch refuses.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr {
    #[logic]
    fn m(self) -> u32;
}
impl Tr for S {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

impl S {
    pub fn m(self) -> u32 {
        0
    }
}

#[ensures(result == s.m())]
pub fn f(s: S) -> u32 {
    10
}
