//@ expect: reject
//@ verdict: failed
//@ mechanism: the unit struct a bare receiver path denotes is the one the OWNER's module
//@ mechanism: resolves, `use` imports included: `m::inner` imports `m::S` while the crate root
//@ mechanism: defines a different `S` with the same trait and an impl stating the other
//@ mechanism: argument. Resolving the name anywhere but the owner's module picks the wrong impl.
//@ accept-means: `S` was typed as the crate-root `S` (a lookup outside the owner's scope).
//@ WHY THE CONTRACT IS FALSE: `m::S`'s `v(a, b)` is `b` and `g` returns `a`; `g(0, 1)` returns 0.
//@ teeth: standing shape gate for the scope of unit_struct_value_type; not shown to accept on
//@ teeth: any build (no build resolved the name in the wrong module).
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
        pub fn g(a: u32, b: u32) -> u32 { a }
    }
}
