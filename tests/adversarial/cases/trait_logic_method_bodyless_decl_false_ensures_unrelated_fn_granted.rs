//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: a bodyless trait logic method whose `ensures` is unsatisfiable, in a crate with no
//@ mechanism: impl of it. Since D-110 the declaration's postcondition is owed by the implementations
//@ mechanism: and is no longer checked against the placeholder a declaration carries, so with no impl
//@ mechanism: its axiom stands. It says something only about `Tr::m`: a goal that never names the
//@ mechanism: method must not carry it, or `forall self. false` would prove every contract in the crate.
//@ fixed-by: n/a (regression guard for D-110's bodyless-declaration rule)
//@ accept-means: `f` returns 0 and claims 1; nothing in it names `Tr::m`.
//@ teeth: MEASURED before D-110: rejected as here, the declaration's `ensures` refuted against the placeholder and its axiom withdrawn. At D-110: `Tr::m is a trait logic method declaration (postcondition owed by each implementation)`, and `f FAILED ✗` with the counterexample `result = 0`, so the standing axiom did not reach its goal. The isolating twin trait_logic_method_bodyless_decl_false_ensures_unrelated_fn_control.rs claims 0 and verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(false)]
    fn m(self) -> Int;
}

#[ensures(result == 1i32)]
pub fn f() -> i32 {
    0
}
