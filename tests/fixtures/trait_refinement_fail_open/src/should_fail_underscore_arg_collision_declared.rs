// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (review F1, t2b): the trait's `_` parameter at position 0 was
//! named `arg0`, colliding with the real parameter `arg0` at position 1, so
//! both impl parameters were renamed onto `arg0` and `result == x` matched
//! `result == arg0` verbatim. At runtime `concrete()` returns 1.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result == arg0)]
    fn m(_: u32, arg0: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result == x)]
    fn m(x: u32, y: u32) -> u32 {
        x
    }
}

#[ensures(result == 2u32)]
pub fn through<T: Tr>() -> u32 {
    T::m(1, 2)
}

#[ensures(result == 2u32)]
pub fn concrete() -> u32 {
    through::<S>()
}

fn main() {}
