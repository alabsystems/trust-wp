// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

pub trait Tr {
    #[trust_wp::logic(open, sealed)]
    fn g(&self) -> i32 {
        1
    }
}

impl Tr for () {
    #[trust_wp::logic]
    fn g(&self) -> i32 {
        0
    }
}

fn main() {}
