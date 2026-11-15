//@ expect: verify
//@ mechanism: the over-refusal guard for trait_impl_spec_call_unchecked_std_call_credited. A
//@ mechanism: clause-free `f` calls a contracted trait method whose instance resolves to an impl
//@ mechanism: whose body's only panic site is an addition its own lane owes, so the body is clean
//@ mechanism: and the call is accounted. A fix that refused every call through a trait method would
//@ mechanism: refuse this one too.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓` with D-104.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[requires(x@ < 10)]
    #[ensures(result@ == x@ + 1)]
    fn m(&self, x: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[requires(x@ < 10)]
    #[ensures(result@ == x@ + 1)]
    fn m(&self, x: u32) -> u32 {
        x + 1
    }
}

pub fn f() {
    let _r = S.m(3);
}
