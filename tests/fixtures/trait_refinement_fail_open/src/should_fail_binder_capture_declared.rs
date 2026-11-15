// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (binder capture, declared trait contract): as
//! `should_fail_binder_capture_contractless`, with a declared trait contract.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(true)]
    fn m(x: u32) -> u32;
}

pub struct S;

impl Tr for S {
    #[requires(exists<x: Int> x == y@ && x > 0)]
    #[ensures(true)]
    fn m(y: u32) -> u32 {
        100 / y
    }
}

pub fn through<T: Tr>() -> u32 {
    T::m(0)
}

fn main() {}
