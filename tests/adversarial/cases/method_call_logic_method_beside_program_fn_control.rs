//@ expect: verify
//@ mechanism: control for the bare-call cases: METHOD syntax `s.m()` is the logic method `S::m` (10)
//@ mechanism: whatever the crate root binds `m` to as a free function, and `f` returns 10.
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

pub fn m(_x: S) -> u32 {
    0
}

#[ensures(result == s.m())]
pub fn f(s: S) -> u32 {
    10
}
