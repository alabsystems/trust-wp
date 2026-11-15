// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (fail-open): the trait method has no contract, so its
//! precondition is `true`; the impl adds `x > 0`. A call through
//! `T: Tr` checks nothing, so the impl body would run on `x == 0`.
//! Before WP-07 this was accepted with no refinement check and no error.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    fn m(x: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[requires(x@ > 0)]
    #[ensures(result@ > 0)]
    fn m(x: u32) -> u32 {
        x
    }
}

pub fn through<T: Tr>() -> u32 {
    T::m(0)
}

fn main() {}
