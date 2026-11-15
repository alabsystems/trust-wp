//@ expect: reject
//@ mechanism: the assertion side of bare_call_parameter_read_as_logic_method_granted.rs: `f(s: S, k:
//@ mechanism: fn(S) -> Int)` asserts `k(s) == 10`, where the bare `k` is the parameter, an arbitrary
//@ mechanism: function. The resolver skips a call whose name a parameter binds and leaves it under
//@ mechanism: its written name, and the encoder dispatches the colliding method name `k` on its
//@ mechanism: first argument's sort and reads `<S as Tr>::k(s)` (10): the assertion is proved.
//@ fixed-by: D-199 — REFUSED: a call whose name a parameter or binder binds is that binding, and
//@ fixed-by: the resolver spells it with the refusal marker (`Resolver::resolve_call_name_unchecked`)
//@ fixed-by: instead of leaving it for the encoder's receiver dispatch.
//@ accept-means: the assertion `k(s) == 10` about the parameter `k` is credited and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`proof_assert in creusot_test::f verified ✓`) with D-198 in
//@ teeth: force.
//@ teeth: With D-199: REFUSED (`unknown`): the assertion's `__lfidU__k` is not resolved.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn k(self) -> Int;
}

pub struct S;
impl Tr for S {
    #[logic(open)]
    fn k(self) -> Int {
        pearlite! { 10 }
    }
}

pub fn f(s: S, k: fn(S) -> Int) {
    proof_assert!(k(s) == 10);
}
