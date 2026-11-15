// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (review probe q3): the alias hole of q1 through a tuple
//! binder annotation, which the parser maps to no sort.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports, non_camel_case_types)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod t {
    use creusot_std::prelude::*;
    pub type Wd = u8;
    pub trait Tr {
        #[requires(forall<p: (Wd, bool)> p.0@ < 256)]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    pub type Wd = u64;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(forall<p: (Wd, bool)> p.0@ < 256)]
        fn m(x: u32) -> u32 { x }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(5) }

fn main() {}
