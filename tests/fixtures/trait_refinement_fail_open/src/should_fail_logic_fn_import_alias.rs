// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (import alias): the trait's `k` is `a::z` (0) imported as `k`,
//! the impl's `k` is `b::k` (10); only one logic fn is named `k`.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports)]

extern crate creusot_std;
use creusot_std::prelude::*;
// Only ONE logic fn named k (so no ambiguity refusal); trait scope's `k`
// is a different logic fn imported under that name from a module whose fn is `z`.
pub mod a { use creusot_std::prelude::*; #[logic(open)] pub fn z() -> Int { 0 } }
pub mod b { use creusot_std::prelude::*; #[logic(open)] pub fn k() -> Int { 10 } }
pub mod t {
    use creusot_std::prelude::*;
    use crate::a::z as k;
    pub trait Tr {
        #[requires(x@ > k())]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    use crate::b::k;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(x@ > k())]
        fn m(x: u32) -> u32 { x - 11 }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(5) }

fn main() {}
