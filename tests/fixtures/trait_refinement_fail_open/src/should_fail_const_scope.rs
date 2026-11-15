// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial (constant scope): trait `K` is `a::K` (0), impl `K` is `b::K`
//! (10). Textually identical clauses, different preconditions.

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
}
pub mod i {
    use creusot_std::prelude::*;
    use crate::b::K;
    pub struct S;
    impl crate::t::Tr for S {
        #[requires(x > K)]
        fn m(x: u32) -> u32 { x - 11 }
    }
}
pub fn through<T: t::Tr>() -> u32 { T::m(5) }

fn main() {}
