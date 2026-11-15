// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (review F2, t1b): an impl parameter named `result`. The body
//! path refuses the name; the standalone refinement pass credited it.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(x@ == 0)]
    fn m(x: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ == 0)]
    fn m(result: u32) -> u32 {
        0
    }
}

pub fn through<T: Tr>() -> u32 {
    T::m(5)
}

fn main() {}
