// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: a FREE logic function taking an `impl Trait` argument and calling
//! through it. The bound sits on the free function, not on a method of the
//! trait itself, so no trait-bound cycle exists — legitimate terminating
//! trait-bounded logic must keep compiling.

use trust_wp::logic;

pub trait Cost {
    #[logic]
    fn cost(&self) -> i32;
}

impl Cost for i32 {
    #[logic]
    fn cost(&self) -> i32 {
        1
    }
}

#[logic]
pub fn total(x: impl Cost) -> i32 {
    x.cost()
}

fn main() {}
