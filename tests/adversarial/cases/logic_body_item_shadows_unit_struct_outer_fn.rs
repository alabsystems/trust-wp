//@ expect: reject
//@ mechanism: as logic_body_item_shadows_unit_struct, one level out: `inner` is declared in
//@ mechanism: `outer`'s body, next to a `struct S` that shadows the crate root's for everything
//@ mechanism: in that body, `inner`'s clauses included. The resolver's module lookup skips the
//@ mechanism: enclosing body entirely.
//@ accept-means: `inner`'s clause was read with the module's `S`.
//@ WHY THE CONTRACT IS FALSE: the enclosing body's `S.v(a, b)` is `b`; `inner(0, 1)` returns 0.
//@ teeth: exit-0 false accept on the commit that first typed unit struct receivers; rejected by
//@ teeth: refusal once an enclosing body's item withholds the module's answer.
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
pub fn outer() -> u32 {
    struct S;
    impl Tr for S {
        #[logic(open)]
        fn v(self, _: Int, q: Int) -> Int { q }
    }
    #[ensures(result@ == S.v(a@, b@))]
    fn inner(a: u32, b: u32) -> u32 { a }
    inner(1, 2)
}
