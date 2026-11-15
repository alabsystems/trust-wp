//@ expect: verify
//@ xfail: a name the owner's body redeclares is refused, not resolved: shadowed_by_body_item
//@ xfail: withholds the module's answer, and nothing resolves the body's own item (that needs to
//@ xfail: tell an item of the body's top-level block from one in an inner block, which the DefId
//@ xfail: tree does not record). This TRUE twin of logic_body_item_shadows_unit_struct pays it.
//@ mechanism: the TRUE twin of logic_body_item_shadows_unit_struct: the body's `S.v(a, b)` is `b`,
//@ mechanism: and `g` returns it.
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
    struct S;
    impl Tr for S {
        #[logic(open)]
        fn v(self, _: Int, q: Int) -> Int { q }
    }
    b
}
