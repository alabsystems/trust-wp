// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (call path of review F1): the trait's `_` parameter at
//! position 1 was named `arg1`, colliding with the real parameter `arg1` at
//! position 0. Call sites bind clause names by parameter name, later names
//! winning, so `arg1` in the trait postcondition was bound to the second
//! argument. `through` returns 1 at runtime, never 2.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result == arg1)]
    fn m(arg1: u32, _: u32) -> u32;
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

fn main() {}
