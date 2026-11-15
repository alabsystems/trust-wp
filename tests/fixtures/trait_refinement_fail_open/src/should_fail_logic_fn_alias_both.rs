// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (alias on both sides): `j` is `a::k` in the trait module and
//! `b::k` in the impl module.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod a { use creusot_std::prelude::*; #[logic(open)] pub fn k() -> Int { 0 } }
pub mod b { use creusot_std::prelude::*; #[logic(open)] pub fn k() -> Int { 10 } }
pub mod t {
    use creusot_std::prelude::*;
    use crate::a::k as j;
    pub trait Tr {
        #[requires(x@ > j())]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    use crate::b::k as j;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(x@ > j())]
        fn m(x: u32) -> u32 { x - 11 }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(5) }

fn main() {}
