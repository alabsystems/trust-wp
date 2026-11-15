//@ expect: verify
//@ mechanism: control for the h_forged_spec_tc_* family — the genuine macro-generated type-check
//@ mechanism: vehicles (a bodyless trait-method contract's sibling helper, a closure contract's
//@ mechanism: type-check closure) carry macro-emitted markers and must keep being honoured
//@ fixed-by: 09ee89eb
//@ teeth: over-refusal gate — a provenance check too strict for the real vehicles refuses this
//@ teeth: file with the reserved-marker frontend error (exit 2)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait T {
    #[requires(x@ < 10)]
    #[ensures((^y)@ == x@)]
    fn m(&self, x: u32, y: &mut u32);
}

pub struct S;

impl T for S {
    #[requires(x@ < 10)]
    #[ensures((^y)@ == x@)]
    fn m(&self, x: u32, y: &mut u32) {
        *y = x;
    }
}

#[ensures(result@ == 3)]
pub fn user(s: &S) -> u32 {
    let mut v = 0u32;
    s.m(3, &mut v);
    let c = #[requires(a@ < 100)]
    #[ensures(result@ == a@ + 1)]
    |a: u32| -> u32 { a + 1 };
    let _ = c(1);
    v
}
