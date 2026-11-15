// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (binder capture): the impl renames the trait parameter `x`
//! to `y` and its requires binds `x`. The real goal is `true => y@ > 0`,
//! which is invalid (`through` calls with 0). A non-capture-avoiding rename
//! `y := x` turns the clause into the tautology `exists<x> x == x && x > 0`.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    fn m(x: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[requires(exists<x: Int> x == y@ && x > 0)]
    fn m(y: u32) -> u32 {
        100 / y
    }
}

pub fn through<T: Tr>() -> u32 {
    T::m(0)
}

fn main() {}
