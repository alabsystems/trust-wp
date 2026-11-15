// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial: a cast to the alias `Wd`, which is `u8` in the trait's module
//! and `u32` in the impl's. Identical texts; x = 256 satisfies the trait
//! precondition only.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports, non_camel_case_types)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod t {
    use creusot_std::prelude::*;
    pub type Wd = u8;
    pub trait Tr {
        #[requires((x as Wd)@ == 0)]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    pub type Wd = u32;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires((x as Wd)@ == 0)]
        fn m(x: u32) -> u32 { x }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(256) }

fn main() {}
