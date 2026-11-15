//@ expect: verify
//@ mechanism: control for the method-lookup cases: `s.m()` on a receiver of type `S` itself, where
//@ mechanism: `S` has an inherent logic `m(self)` (0) and inherits Tr1's default `m` (10). Rust's
//@ mechanism: lookup takes the inherent method at the first step, by value, before any trait method,
//@ mechanism: and `f` returns 0.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
//@ xfail: the price of D-161 in D-208: Tr1's default body runs at `S` and is counted as a candidate
//@ xfail: beside the inherent `m`, so the receiver lookup refuses where Rust's lookup takes the
//@ xfail: inherent method at the first step, by value.
//@ xfail-verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr1 {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}
impl Tr1 for S {}

impl S {
    #[logic(open)]
    pub fn m(self) -> u32 {
        pearlite! { 0u32 }
    }
}

#[ensures(result == s.m())]
pub fn f(s: S) -> u32 {
    0
}
