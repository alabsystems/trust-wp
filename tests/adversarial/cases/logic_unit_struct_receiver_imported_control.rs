//@ expect: verify
//@ mechanism: the TRUE twin of logic_unit_struct_receiver_imported: the imported `m::S`'s impl
//@ mechanism: states the second argument, and `g` returns it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self, p: Int, q: Int) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn v(self, p: Int, _: Int) -> Int { p }
}
pub mod m {
    use creusot_std::prelude::*;
    use super::Tr;
    pub struct S;
    impl Tr for S {
        #[logic(open)]
        fn v(self, _: Int, q: Int) -> Int { q }
    }
    pub mod inner {
        use creusot_std::prelude::*;
        use super::super::Tr;
        use super::S;
        #[ensures(result@ == S.v(a@, b@))]
        pub fn g(a: u32, b: u32) -> u32 { b }
    }
}
