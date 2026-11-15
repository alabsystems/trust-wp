//@ expect: reject
//@ verdict: failed
//@ fn-failed: <A as Tr>::m
//@ mechanism: a contracted trait LOGIC method's `ensures` is owed by every logic impl, and no impl
//@ mechanism: was asked for it. `<A as Tr>::m` is registered as a logic function with no `ensures` of
//@ mechanism: its own (the contract loop's `LogicFnAxiom` arm), so its body `-1` was never checked
//@ mechanism: against the inherited `result >= 0`; the refinement pass found the inherited clause
//@ mechanism: verbatim and reported it refined. `gen_m`'s postcondition rests on the trait method's
//@ mechanism: `ensures` for every `T: Tr`. The bodyless declaration `Tr::m` was itself printed
//@ mechanism: `verified ✓`: the logic pass checked its `ensures` against the placeholder `0` a
//@ mechanism: declaration carries in place of a body.
//@ fixed-by: D-110 (each local logic impl owes `D.requires => D.ensures` at `result := I(params)`; one that does not withdraws the declaration's axiom)
//@ accept-means: `gen_m` claims `t.m() >= 0` for every `T: Tr`; at `T = A` the only impl makes `m` equal `-1`.
//@ teeth: MEASURED at the parent commit: ACCEPTED with exit 0, `creusot_test::Tr::m verified ✓` and `gen_m verified ✓`; the same crate with A's body `1` printed the identical lines. At the fix, `<A as Tr>::m FAILED ✗ (postcondition of trait logic method `Tr::m`)`, the axiom is withheld and `gen_m` is `unknown`. The isolating twin trait_logic_method_ensures_discharged_by_logic_impl_control.rs (A's body `1`) verifies. Sibling of trait_logic_impl_of_program_method_granted.rs (a logic impl of a PROGRAM trait method) and of trait_logic_method_own_ensures_impl_refuted_granted.rs (an impl whose own clause is the refuted one).
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
    #[logic(open)]
    fn m(self) -> Int {
        pearlite! { -1 }
    }
}

#[ensures(t.m() >= 0)]
pub fn gen_m<T: Tr>(t: T) {}
