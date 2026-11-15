//@ expect: reject
//@ mechanism: both halves at once (D-122 and D-123): the closure `Option::map` runs is written in an inline
//@ mechanism: `const { }` inside a trait impl. The escape scan must read it as program code (the
//@ mechanism: owner walk goes out through the const), and the escape join's withdrawal of the impl
//@ mechanism: must reach the trait join, which withdraws `generic_caller`.
//@ accept-means: `<S as Tr>::m` and `generic_caller` are reported `verified` although
//@ accept-means: `generic_caller(&S, Some(5))` panics with "index out of bounds".
//@ WHY THE CONTRACT IS FALSE: `generic_caller::<S>(&S, Some(5))` runs `[1u32, 2][5]`.
//@ fixed-by: D-122 and D-123.
//@ teeth: MEASURED: ACCEPTED, exit 0, on the binary before both, with `<S as Tr>::m verified ✓`
//@ teeth: and `generic_caller verified ✓`. After them the const-owned closure is not proved,
//@ teeth: `<S as Tr>::m` is withdrawn and `generic_caller` with it.
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

pub trait Tr {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>) -> u32 {
        let _ = o.map(const { |j: usize| [1u32, 2][j] });
        1
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>) -> u32 {
    t.m(o)
}
