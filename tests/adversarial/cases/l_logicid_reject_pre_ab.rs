//@ expect: reject
//@ mechanism: logic-fn identity — caller precondition of a callee whose requires names a colliding logic fn `k`; callee text re-parsed at the call site (definition order ab)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: a clause was checked against another definition that shares the short name
//@ teeth: accepted with exit 0 on wp-campaign fd7534d in at least one definition order (see s35 progress.md)
//@ also-verified: b::g
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn k() -> Int { pearlite!{0} }
}
pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn k() -> Int { pearlite!{10} }
    #[requires(x@ > k())]
    #[ensures(true)]
    pub fn g(x: u32) {}
    #[ensures(true)]
    pub fn caller() { g(5) }
}
