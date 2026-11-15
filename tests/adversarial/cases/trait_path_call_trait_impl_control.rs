//@ expect: verify
//@ mechanism: control for the trait-path cases: `Tr1::m(s)` and `<S as Tr1>::m(s)` with Tr1
//@ mechanism: implemented for `S` by an impl member (10), and no competing definition; both functions
//@ mechanism: return 10.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1 {
    #[logic]
    fn m(self) -> u32;
}
impl Tr1 for S {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

#[ensures(result == Tr1::m(s))]
pub fn f(s: S) -> u32 {
    10
}

#[ensures(result == <S as Tr1>::m(s))]
pub fn g(s: S) -> u32 {
    10
}
