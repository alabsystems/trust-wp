// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (name scope): the trait clause's `k` is `a::k` (0) and the
//! impl clause's `k` is `b::k` (10). The textually identical clauses state
//! different preconditions: `through` calls with 5 and the body underflows.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        0
    }
}

pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        10
    }
}

pub mod t {
    use crate::a::k;
    use creusot_std::prelude::*;
    pub trait Tr {
        #[requires(x@ > k())]
        fn m(x: u32) -> u32;
    }
}

pub mod i {
    use crate::b::k;
    use creusot_std::prelude::*;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(x@ > k())]
        fn m(x: u32) -> u32 {
            x - 11
        }
    }
}

pub fn through<T: t::Tr>() -> u32 {
    T::m(5)
}

fn main() {}
