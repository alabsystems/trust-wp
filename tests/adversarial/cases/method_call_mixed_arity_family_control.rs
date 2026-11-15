//@ expect: verify
//@ mechanism: control: the family holds the method `S::m` (10) and the free logic function
//@ mechanism: `other::m(a, b)` (5). Method syntax `s.m()` is Rust's method lookup on `s`, which
//@ mechanism: selects `S::m`, and `f` returns 10.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;
impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

pub mod other {
    use crate::S;
    use creusot_std::prelude::*;

    #[logic(open)]
    pub fn m(_a: S, _b: S) -> u32 {
        pearlite! { 5u32 }
    }
}

#[ensures(result == s.m())]
pub fn f(s: S) -> u32 {
    let _ = s;
    10
}
