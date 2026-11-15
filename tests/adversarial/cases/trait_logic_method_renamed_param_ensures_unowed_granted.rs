//@ expect: reject
//@ verdict: failed
//@ fn-failed: <A as Tr>::m
//@ mechanism: the parameterised spelling of trait_logic_method_ensures_unowed_by_logic_impl.rs. The
//@ mechanism: declaration `m(self, x)` requires `x >= 0` and ensures `result <= x`; A's logic impl
//@ mechanism: names the parameter `y` and returns `y + 1`, which violates the postcondition at every
//@ mechanism: admitted argument. The check that each logic impl owes `D.requires => D.ensures` at
//@ mechanism: `result := I(params)` must rename the declaration's `x` to the impl's `y` position by
//@ mechanism: position, and must use the requires as a premise and nothing else: the placeholder a
//@ mechanism: declaration carries (0) satisfies the clause under the requires, so a check that reads
//@ mechanism: the declaration and not the impl proves it.
//@ fixed-by: D-110 (each local logic impl owes its trait logic method's postcondition)
//@ accept-means: `g` claims `t.m(5) <= 5` for every `T: Tr`; at `T = A` the only impl makes it 6.
//@ teeth: MEASURED before D-110: `creusot_test::Tr::m verified ✓` against the placeholder and `g verified ✓`, rejected only by the refinement check's refusal of the impl's parameter name. At D-110: `<A as Tr>::m FAILED ✗ (postcondition of trait logic method `Tr::m`)`, the axiom is withheld and `g` is `unknown`. The isolating twin trait_logic_method_renamed_param_ensures_discharged_control.rs (A returns `y - 1`) verifies at D-110 and was not verified before it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[requires(x >= 0)]
    #[ensures(result <= x)]
    fn m(self, x: Int) -> Int;
}

pub struct A;

impl Tr for A {
    #[logic(open)]
    fn m(self, y: Int) -> Int {
        pearlite! { y + 1 }
    }
}

#[ensures(t.m(5) <= 5)]
pub fn g<T: Tr>(t: T) {}
