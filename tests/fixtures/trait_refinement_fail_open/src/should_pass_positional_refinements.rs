// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Refining impls under positional parameter renaming: underscore trait
//! parameters with no collision, receivers, and swapped names.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Under {
    #[requires(y@ > 10)]
    #[ensures(result@ > 0)]
    fn m(_: u32, y: u32) -> u32;
}

pub struct U;

impl Under for U {
    #[requires(b@ > 5)]
    #[ensures(result@ > 5)]
    fn m(a: u32, b: u32) -> u32 {
        b
    }
}

pub trait Recv {
    #[requires(x@ < 100)]
    #[ensures(result@ == x@)]
    fn m(&self, x: u32) -> u32;
}

pub struct R;

impl Recv for R {
    #[requires(y@ < 100)]
    #[ensures(result@ == y@)]
    fn m(&self, y: u32) -> u32 {
        y
    }
}

pub trait Cross {
    #[requires(x@ < y@)]
    #[ensures(result@ == y@ - x@)]
    fn m(x: u32, y: u32) -> u32;
}

pub struct X;

impl Cross for X {
    #[requires(y@ < x@)]
    #[ensures(result@ == x@ - y@)]
    fn m(y: u32, x: u32) -> u32 {
        x - y
    }
}

fn main() {}
