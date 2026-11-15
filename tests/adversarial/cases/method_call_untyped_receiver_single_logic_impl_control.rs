//@ expect: verify
//@ mechanism: control for the encoder's receiver dispatch: `w.0.m()` where `S`'s only `m` is the
//@ mechanism: logic `<S as Tr>::m` (10), and `f` returns 10.
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

pub struct Wrap(pub S);

pub trait Tr {
    #[logic]
    fn m(self) -> u32;
}
impl Tr for S {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

#[ensures(result == w.0.m())]
pub fn f(w: Wrap) -> u32 {
    10
}
