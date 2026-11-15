// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (constant scope, with a caller through the trait): the
//! refinement must not be credited.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod a { pub const K: u32 = 0; }
pub mod b { pub const K: u32 = 10; }
pub mod t {
    use creusot_std::prelude::*;
    use crate::a::K;
    pub trait Tr {
        #[requires(x > K)]
        fn m(x: u32) -> u32;
    }
    // Trait precondition 5 > 0 holds; the impl body then underflows.
    #[requires(true)]
    pub fn caller<T: Tr>() -> u32 { T::m(5) }
}
pub mod i {
    use creusot_std::prelude::*;
    use crate::b::K;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(x > K)]
        #[ensures(result@ == x@ - 11)]
        fn m(x: u32) -> u32 { x - 11 }
    }
}
#[requires(true)]
pub fn concrete() -> u32 { t::caller::<i::S>() }

fn main() {}
