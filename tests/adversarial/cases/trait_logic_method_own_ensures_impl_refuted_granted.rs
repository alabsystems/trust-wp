//@ expect: reject
//@ verdict: failed
//@ fn-failed: <A as Tr>::m
//@ mechanism: a logic impl that restates its trait logic method's `ensures` and refutes it. The logic
//@ mechanism: pass checks the impl's OWN clause, fails it, and withholds the IMPL's axiom; the trait
//@ mechanism: declaration's axiom, which is what a generic consumer is handed, stood, because no
//@ mechanism: impl owed it. `gen_m` rests on it for every `T: Tr`.
//@ fixed-by: D-110 (the impl owes the declaration's postcondition whatever clauses it states)
//@ accept-means: `gen_m` claims `t.m() >= 0` for every `T: Tr`; at `T = A` the only impl makes `m` equal `-1`.
//@ teeth: MEASURED at the parent commit: `creusot_test::<A as Tr>::m postcondition FAILED (logic postcondition)` beside `creusot_test::Tr::m verified ✓` and `gen_m verified ✓`, with no withdrawal. The control is trait_logic_method_ensures_discharged_by_logic_impl_control.rs.
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
    #[ensures(result >= 0)]
    fn m(self) -> Int {
        pearlite! { -1 }
    }
}

#[ensures(t.m() >= 0)]
pub fn gen_m<T: Tr>(t: T) {}
