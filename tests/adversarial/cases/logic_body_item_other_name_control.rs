//@ expect: verify
//@ mechanism: the boundary of shadowed_by_body_item: the body declares an item and an impl, but
//@ mechanism: under ANOTHER name, so the clause's `S` is still the module's and resolves to its
//@ mechanism: impl. What withholds the module's answer is a redeclaration of the name, not the
//@ mechanism: presence of body items.
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
#[ensures(result@ == S.v(a@, b@))]
pub fn g(a: u32, b: u32) -> u32 {
    struct W;
    impl Tr for W {
        #[logic(open)]
        fn v(self, _: Int, q: Int) -> Int { q }
    }
    a
}
