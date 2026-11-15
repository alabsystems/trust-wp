//@ expect: reject
//@ mechanism: a contract clause is type-checked at the head of its owner's body (the spec_tc
//@ mechanism: closure, where Creusot inserts its spec item too), so a `struct S` declared in that
//@ mechanism: body is the `S` the clause names. The logic-identity resolver looked `S` up through
//@ mechanism: the owner's MODULE, found the crate root's unit struct, and resolved `S.v` to ITS impl
//@ mechanism: (logic/identity.rs shadowed_by_body_item now withholds the module's answer).
//@ accept-means: the clause was read with the module's `S` although the body's `S` shadows it.
//@ WHY THE CONTRACT IS FALSE: the body's `S.v(a, b)` is `b`; `g(0, 1)` returns 0.
//@ teeth: exit-0 false accept on the commit that first typed unit struct receivers (the module
//@ teeth: lookup alone); rejected by refusal once the body item withholds it.
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
    a
}
