// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (review probe q1): the binder type `Wd` is `u8` in the trait's
//! module and `u64` in the impl's. The trait precondition is true, the impl's
//! is false; the texts and the parsed ASTs are identical.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports, non_camel_case_types)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod t {
    use creusot_std::prelude::*;
    pub type Wd = u8;
    pub trait Tr {
        #[requires(forall<v: Wd> v@ < 256)]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    pub type Wd = u64;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(forall<v: Wd> v@ < 256)]
        fn m(x: u32) -> u32 { x }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(5) }

fn main() {}
