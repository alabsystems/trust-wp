// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (review probe q4): the trait requires `(x as u8)@ == 0`, the
//! impl `x@ == 0`. x = 256 satisfies the trait's and not the impl's. The
//! parser once erased the cast, making the ASTs identical; it now lowers it to
//! Rust's `as`, and the refinement check refuses a written cast either way.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports, non_camel_case_types)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod t {
    use creusot_std::prelude::*;
    pub trait Tr {
        #[requires((x as u8)@ == 0)]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(x@ == 0)]
        fn m(x: u32) -> u32 { x }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(256) }

fn main() {}
