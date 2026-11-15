//@ expect: reject
//@ mechanism: the trait-path spelling of program_ensures_ufcs_two_impls_read_as_one.rs: `Tr::m(x) == Other::m(x)` in a program function's `ensures`, where `S` implements two traits that each declare `m(self)`. Both calls are path calls spelled `m` with one argument `x`; D-163's confirmation matched a path call with rustc's calls by name, arity and first argument, so the two pooled, neither reading was confirmed, and both refusals were one symbol: `__lfidU__m(x) == __lfidU__m(x)`, which the trivially-true check proves without encoding it.
//@ accept-means: a program function is credited with the equality of two traits' methods of one name, and the crate exits 0.
//@ WHY IT IS FALSE: `<S as Tr>::m(x)` is `1` and `<S as Other>::m(x)` is `2`.
//@ teeth: MEASURED ACCEPTED, exit 0 (`prog verified ✓`) at D-163 with path calls pooled by their first argument. Refuted (`failed`) with each path call confirmed against rustc's calls of its own written path; refused (`unknown`) with the paths still pooled but each refusal its own symbol. The control, program_ensures_two_trait_paths_one_name_control.rs, verifies only with the path rule.
//@ fixed-by: D-164 — a path call is confirmed only by rustc's calls of the same written callee path.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn m(self) -> Int;
}
pub trait Other {
    #[logic]
    fn m(self) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn m(self) -> Int {
        1
    }
}
impl Other for S {
    #[logic(open)]
    fn m(self) -> Int {
        2
    }
}

#[ensures(Tr::m(x) == Other::m(x))]
pub fn prog(x: S) {}
