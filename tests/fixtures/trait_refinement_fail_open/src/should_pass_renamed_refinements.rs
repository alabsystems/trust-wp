// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Refining impls whose parameters are renamed relative to the trait.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Same {
    #[requires(x@ > 0)]
    #[ensures(result@ > 0)]
    fn m(x: u32) -> u32;
}

pub struct A;

impl Same for A {
    #[requires(y@ > 0)]
    #[ensures(result@ > 0)]
    fn m(y: u32) -> u32 {
        y
    }
}

pub trait Refine {
    #[requires(x@ > 10)]
    #[ensures(result@ > 0)]
    fn m(x: u32) -> u32;
}

pub struct B;

impl Refine for B {
    #[requires(y@ > 5)]
    #[ensures(result@ > 5)]
    fn m(y: u32) -> u32 {
        y
    }
}

pub trait Quant {
    #[requires(x@ < 50)]
    fn m(x: u32) -> u32;
}

pub struct C;

impl Quant for C {
    #[requires(forall<i: Int> 0 <= i && i < y@ ==> i < 100)]
    fn m(y: u32) -> u32 {
        y
    }
}

pub trait Swap {
    #[requires(x@ < y@)]
    fn m(x: u32, y: u32) -> u32;
}

pub struct D;

impl Swap for D {
    #[requires(y@ < x@)]
    fn m(y: u32, x: u32) -> u32 {
        x - y
    }
}

fn main() {}
