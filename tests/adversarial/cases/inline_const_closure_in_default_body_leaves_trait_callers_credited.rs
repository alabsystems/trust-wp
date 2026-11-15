//@ expect: reject
//@ mechanism: both halves at once, on a trait DEFAULT body: `Dt::m` hands `Option::map` a closure
//@ mechanism: written in an inline `const { }`. The escape scan must read the closure as program
//@ mechanism: code (its owner walk goes out through the const to `Dt::m`, D-123), and the escape
//@ mechanism: join's withdrawal of the default body must reach the trait join, which withdraws
//@ mechanism: `default_caller`, run with `D`, which keeps the default (D-122).
//@ accept-means: `Dt::m` and `default_caller` are reported `verified` although
//@ accept-means: `default_caller(&D, Some(5))` panics with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `default_caller::<D>(&D, Some(5))` runs `[1u32, 2][5]`.
//@ fixed-by: D-122 and D-123.
//@ teeth: MEASURED: ACCEPTED, exit 0, on the binary before both, with `Dt::m verified ✓` and
//@ teeth: `default_caller verified ✓`. After them the closure `Dt::m::{constant#0}::{closure#0}`
//@ teeth: is not proved, `Dt::m` is withdrawn and `default_caller` with it ("it assumed trait
//@ teeth: method contract `Dt::m`").
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

pub trait Dt {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>) -> u32 {
        let _ = o.map(const { |j: usize| [1u32, 2][j] });
        1
    }
}

pub struct D;

impl Dt for D {}

#[ensures(result@ == 1)]
pub fn default_caller<T: Dt>(t: &T, o: Option<usize>) -> u32 {
    t.m(o)
}
