//@ expect: reject
//@ mechanism: the assertion spelling of program_ensures_ufcs_two_impls_read_as_one.rs: `proof_assert!(<S as Tr>::m(x@) == <U as Tr>::m(x@))`. The two qualified calls share a name, an arity and the argument `x@`; matched with rustc's calls by those, neither reading was confirmed, and the two refusals were one symbol, so the assertion read `__lfidU__m(x@) == __lfidU__m(x@)` and was proved without encoding either call.
//@ accept-means: an assertion equating two implementations of one trait method is reported verified, and the crate exits 0.
//@ WHY IT IS FALSE: `<S as Tr>::m(x@)` is `x@ + 1` and `<U as Tr>::m(x@)` is `x@`.
//@ teeth: MEASURED ACCEPTED, exit 0 (`proof_assert in creusot_test::prog verified ✓`) at D-163 with path calls pooled by their first argument. Refuted (`failed`) with each confirmed against rustc's calls of its own written path. The control, proof_assert_ufcs_two_impls_read_as_one_control.rs, verifies only with the path rule.
//@ fixed-by: D-164 — a path call is confirmed only by rustc's calls of the same written callee path.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn m(x: Int) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn m(x: Int) -> Int {
        x + 1
    }
}
pub struct U;
impl Tr for U {
    #[logic(open)]
    fn m(x: Int) -> Int {
        x
    }
}

pub fn prog(x: u32) {
    proof_assert!(<S as Tr>::m(x@) == <U as Tr>::m(x@));
}
