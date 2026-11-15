// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial: the trait's module shadows the prelude `Int` with `u8`, so the
//! identical binder `forall<v: Int>` ranges over different types on the two
//! sides. The trait precondition is true (every u8 is below 256), the impl's
//! is `x@ > 0`; x = 0 satisfies the trait precondition only. `Int` is
//! accepted only while no item or import in the crate shadows it.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables, unused_imports, non_camel_case_types)]

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod t {
    use creusot_std::prelude::*;
    pub type Int = u8;
    pub trait Tr {
        #[requires(x@ > 0 || forall<v: Int> v@ < 256)]
        fn m(x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(x@ > 0 || forall<v: Int> v@ < 256)]
        fn m(x: u32) -> u32 { x - 1 }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(0) }

fn main() {}
