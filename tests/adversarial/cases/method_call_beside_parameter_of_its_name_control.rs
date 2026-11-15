//@ expect: verify
//@ mechanism: control: `f(s: S, k: fn(S) -> Int)` claims `result@ == s.k()`. Method syntax is
//@ mechanism: Rust's method lookup on `s`, which a value binding named `k` does not touch: it is
//@ mechanism: `<S as Tr>::k` (10), and `f` returns 10.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
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

#[ensures(result@ == s.k())]
pub fn f(s: S, k: fn(S) -> Int) -> u32 {
    10
}
