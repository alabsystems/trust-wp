// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result@ > 0)]
    fn m(&self) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ >= 0)]
    fn m(&self) -> u32 {
        0
    }
}

fn main() {}
