// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial: the trait requires `255u8 + 1u8 == 0u8` (true: pearlite
//! machine-integer addition wraps), the impl `255u16 + 1u16 == 0u16`
//! (false). The parser keeps literal values and drops their suffixes, so the
//! ASTs are identical and the verbatim shortcut would drop the goal.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports, non_camel_case_types)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod t {
    use creusot_std::prelude::*;
    pub trait Tr {
        #[requires(255u8 + 1u8 == 0u8)]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(255u16 + 1u16 == 0u16)]
        fn m(x: u32) -> u32 { x }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(0) }

fn main() {}
