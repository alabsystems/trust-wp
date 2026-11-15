//@ expect: verify
//@ mechanism: a bodyless trait logic method whose `ensures` the placeholder body a declaration
//@ mechanism: carries (`0`) does not satisfy. The logic pass used to check the clause against that
//@ mechanism: placeholder, fail it, and withdraw the axiom, so `gen_m` could not use the trait's
//@ mechanism: postcondition at all. The postcondition is owed by each implementation, and this crate
//@ mechanism: has none, so the axiom stands and `gen_m` verifies, as it does under Creusot.
//@ fixed-by: D-110 (a bodyless, non-law trait logic method is not checked against a placeholder)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED at the parent commit as `creusot_test::Tr::m postcondition FAILED (logic postcondition)` and `gen_m unknown`)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result > 0)]
    fn m(self) -> Int;
}

#[ensures(t.m() > 0)]
pub fn gen_m<T: Tr>(t: T) {}
