//@ expect: reject
//@ verdict: failed
//@ fn-failed: <A as Tr>::m
//@ mechanism: a bodyless contracted trait LOGIC method implemented by a plain program `fn`, which the
//@ mechanism: logic-marker check accepts (the impl inherits logic-ness). The declaration's
//@ mechanism: `result@ >= 0` is an axiom handed to `gen_m` for every `T: Tr`. The impl's program body
//@ mechanism: owes the inherited clause and fails it, but that verdict withdraws only callers of the
//@ mechanism: program method; the axiom `gen_m` rests on was owed by no check of the implementation,
//@ mechanism: because the check that owes it looked only at impls the logic model registered as logic
//@ mechanism: functions. An implementation the logic model cannot read discharges nothing.
//@ fixed-by: D-110 (an implementation that is not a logic function the logic model can read discharges no trait logic postcondition)
//@ accept-means: `gen_m` claims `t.m()@ >= 0` for every `T: Tr`; at `T = A` the only impl returns `-1`.
//@ teeth: MEASURED at the parent of D-110: `<A as Tr>::m FAILED ✗ (postcondition)` beside `gen_m verified ✓`, a credit the per-function gate reads as TEETH LOST. At the fix the axiom is withheld (`<A as Tr>::m` was not checked against it) and `gen_m` is not credited. Creusot refuses the pair outright (a program function cannot implement a logic trait method), so there is no true twin that should verify; trait_logic_method_ensures_discharged_by_logic_impl_control.rs is the logic-impl control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result@ >= 0)]
    fn m(self) -> i32;
}

pub struct A;

impl Tr for A {
    fn m(self) -> i32 {
        -1
    }
}

#[ensures(t.m()@ >= 0)]
pub fn gen_m<T: Tr>(t: T) {}
