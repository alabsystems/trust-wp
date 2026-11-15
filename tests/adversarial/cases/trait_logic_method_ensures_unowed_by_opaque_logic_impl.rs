//@ expect: reject
//@ verdict: failed
//@ fn-failed: <A as Tr>::m
//@ mechanism: the opaque spelling of trait_logic_method_ensures_unowed_by_logic_impl.rs. `<A as Tr>::m`
//@ mechanism: is a `#[logic]` impl whose body only its own module may read, and it is the only
//@ mechanism: implementation of the contracted trait logic method `Tr::m`. The declaration's
//@ mechanism: `result >= 0` is an axiom handed to `gen_m` for every `T: Tr`; no check asked the
//@ mechanism: impl's body `-1` for it, and an opaque body is one no consumer outside the impl's module
//@ mechanism: could have refuted it with either. The check that owes the axiom must read the body in
//@ mechanism: the impl's own scope, as the logic pass reads an opaque function's own postcondition.
//@ fixed-by: D-110 (each local logic impl owes `D.requires => D.ensures` at `result := I(params)`, its body read in its own module)
//@ accept-means: `gen_m` claims `t.m() >= 0` for every `T: Tr`; at `T = A` the only impl makes `m` equal `-1`.
//@ teeth: MEASURED at the parent of D-110: ACCEPTED with exit 0, `gen_m verified ✓` and no withdrawal. At the fix `<A as Tr>::m FAILED ✗ (postcondition of trait logic method `Tr::m`)`, the axiom is withheld and `gen_m` is not credited. The isolating twin trait_logic_method_ensures_discharged_by_opaque_logic_impl_control.rs (A's body `1`) verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result >= 0)]
    fn m(self) -> Int;
}

pub struct A;

impl Tr for A {
    #[logic]
    fn m(self) -> Int {
        pearlite! { -1 }
    }
}

#[ensures(t.m() >= 0)]
pub fn gen_m<T: Tr>(t: T) {}
