// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (review F1, t2): contractless trait with a `_` parameter next
//! to a real parameter `arg0`; the impl requires `x == y`, which the trait
//! precondition `true` does not imply.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    fn m(_: u32, arg0: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[requires(x == y)]
    fn m(x: u32, y: u32) -> u32 {
        0
    }
}

pub fn through<T: Tr>() -> u32 {
    T::m(1, 2)
}

fn main() {}
