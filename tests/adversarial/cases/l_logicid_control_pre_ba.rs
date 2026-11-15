//@ expect: verify
//@ mechanism: logic-fn identity — caller precondition of a callee whose requires names a colliding logic fn `k`; callee text re-parsed at the call site (definition order ba)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: n/a (control): the true claim about the resolved definition must verify
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn k() -> Int { pearlite!{10} }
    #[requires(x@ > k())]
    #[ensures(true)]
    pub fn g(x: u32) {}
    #[ensures(true)]
    pub fn caller() { g(11) }
}
pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn k() -> Int { pearlite!{0} }
}
