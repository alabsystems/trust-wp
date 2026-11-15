// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

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
    #[requires(x@ > 0)]
    #[ensures(result@ > 0)]
    fn m(x: u32) -> u32 {
        x
    }
}

pub trait Refine {
    #[requires(x@ > 10)]
    #[ensures(result@ > 0)]
    fn m(x: u32) -> u32;
}

pub struct B;

impl Refine for B {
    #[requires(x@ > 5)]
    #[ensures(result@ > 5)]
    fn m(x: u32) -> u32 {
        x
    }
}

pub trait Open {
    fn m(x: u32) -> u32;
}

pub struct C;

impl Open for C {
    #[ensures(result == x)]
    fn m(x: u32) -> u32 {
        x
    }
}

fn main() {}
